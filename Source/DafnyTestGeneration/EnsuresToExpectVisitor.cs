using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Dafny;
using Errors = Microsoft.Dafny.Errors;
using Function = Microsoft.Dafny.Function;
using Parser = Microsoft.Dafny.Parser;
using Program = Microsoft.Dafny.Program;
using DafnyServer;

namespace DafnyTestGeneration {

    public class EnsuresToExpectVisitor : TopDownVisitor<EnsVisitorState> {

        private Dictionary<string, HashSet<Expression>> memberDeclNameToValidEnsMapper =
            new Dictionary<string, HashSet<Expression>>();
        private Dictionary<string, List<MemberDecl>> classNameToGhostMemberMapper =
            new Dictionary<string, List<MemberDecl>>();
        private Dictionary<string, (List<Microsoft.Dafny.Formal>, 
            List<Microsoft.Dafny.Formal>)> memberDeclNameToInsOutMapper = 
            new Dictionary<string, (List<Microsoft.Dafny.Formal>, 
            List<Microsoft.Dafny.Formal>)>();

        public EnsuresToExpectVisitor() {}

        public void Visit(Program p) {
            Visit(p.DefaultModule);
        }

        private void Visit(TopLevelDecl d) {
            if (d is LiteralModuleDecl moduleDecl) {
                moduleDecl.ModuleDef.TopLevelDecls.ForEach(Visit);
                //moduleDecl.Signature.StaticMembers.Values.Iter(Visit);
            } else if (d is TopLevelDeclWithMembers withMembers) {
                FillGhostMemberMapper(withMembers.Members, withMembers);
                // Visit all Methods in member list
                withMembers.Members.OfType<Method>().Iter(Visit);
                // Visit all non-ghost Functions in member list
                // skip ghost Functions since they're not allowed in expect stmts
                withMembers.Members.OfType<Function>()
                    .Where(f => !f.IsGhost).Iter(Visit);
            }
        }

        // populate members (Fields, Functions, Methods) that are Ghost
        public void FillGhostMemberMapper(List<MemberDecl> mList, TopLevelDeclWithMembers t) {
            List<MemberDecl> members = mList.Where(m => m.IsGhost).ToList();
            classNameToGhostMemberMapper.Add(t.FullDafnyName, members);
        }

        // given memberDeclName, return combined list of Ins/Outs for MemberDecl
        public List<Microsoft.Dafny.Formal> GetSigVars(string memberDeclFullDafnyName) {
            (List<Microsoft.Dafny.Formal> Ins, List<Microsoft.Dafny.Formal> Outs) t;
            memberDeclNameToInsOutMapper.TryGetValue(memberDeclFullDafnyName, out t);
            return t.Ins.Concat(t.Outs).ToList();
        }

        public void Visit(MemberDecl mDecl) {
            if (mDecl is Method m) {
                memberDeclNameToInsOutMapper.Add(m.FullDafnyName, (m.Ins, m.Outs));
                HashSet<Expression> validEnsuresExprList = new HashSet<Expression>();
                foreach (var ens in m.Ens) {
                    var s = new EnsVisitorState(m);
                    Visit(ens, s);
                    if (s.State) {
                        validEnsuresExprList.Add(ens.E);
                    }
                }
                memberDeclNameToValidEnsMapper.Add(m.FullDafnyName, validEnsuresExprList);
            } else if (mDecl is Function f) {
                memberDeclNameToInsOutMapper.Add(f.FullDafnyName, (f.Formals, new List<Microsoft.Dafny.Formal>() { f.Result }));
                HashSet<Expression> validEnsuresExprList = new HashSet<Expression>();
                foreach (var ens in f.Ens) {
                    var s = new EnsVisitorState(f);
                    Visit(ens, s);
                    if (s.State) {
                        validEnsuresExprList.Add(ens.E);
                    }
                }
                memberDeclNameToValidEnsMapper.Add(f.FullDafnyName, validEnsuresExprList);
            }
        }

        protected override bool VisitOneExpr(Expression expr, ref EnsVisitorState st) {
            // old expressions can't go in expect statements, so mark invalid
            if (expr is Microsoft.Dafny.OldExpr) {
                st.MarkInvalid();
                return false;
            // ExprDotName is this.someField
            //  go through all known fields of enclosing class,
            //  make sure any fields with matching name are not ghost
            } else if (expr is Microsoft.Dafny.ExprDotName n) {
                List<MemberDecl> memberList;
                classNameToGhostMemberMapper.TryGetValue(st.EnclosingClassFullName, out memberList);
                var res = memberList.OfType<Field>().SingleOrDefault(f => String.Equals(f.Name, n.SuffixName));
                if (res != null) {
                    st.MarkInvalid();
                }
                return false;
            // ApplySuffix is someCallable() or this.someCallable()
            //  if the Lhs is ExprDotName (this.someCallable())
            //      go through all known methods and functions of enclosing class,
            //      make sure any with matching name are not ghost
            //  if the Lhs is NameSegment (someCallable())
            //      go through Ins & Outs of MemberDecl 
            //      make sure any with matching name are not ghost
            //      if you find a match, no need to check class methods or functions
            //      else 
            //          go through all known methods and functions of enclosing class,
            //          make sure any with matching name are not ghost
            //  Before returning, visit all the Args to ensure they don't use ghost Formals
            } else if (expr is Microsoft.Dafny.ApplySuffix app) {
                if (app.Lhs is Microsoft.Dafny.ExprDotName edn) {
                    List<MemberDecl> memberList;
                    classNameToGhostMemberMapper.TryGetValue(st.EnclosingClassFullName, out memberList);
                    var res = memberList.Where(m => m is Method || m is Function)
                        .SingleOrDefault(f => String.Equals(f.Name, edn.SuffixName));
                    if (res != null) {
                        st.MarkInvalid();
                    }
                    Visit(app.Args, st);
                    return false;
                } else if (app.Lhs is Microsoft.Dafny.NameSegment ns) {
                    foreach (Microsoft.Dafny.Formal i in GetSigVars(st.MemberDeclFullDafnyName)) {
                        if (String.Equals(i.Name, ns.Name)) {
                            if (i.IsGhost) {
                                st.MarkInvalid();
                            } 
                            Visit(app.Args, st);
                            return false;
                        }
                    }
                    List<MemberDecl> memberList;
                    classNameToGhostMemberMapper.TryGetValue(st.EnclosingClassFullName, out memberList);
                    var res = memberList.Where(m => m is Method || m is Function)
                        .SingleOrDefault(f => String.Equals(f.Name, ns.Name));
                    if (res != null) {
                        st.MarkInvalid();
                    }
                    Visit(app.Args, st);
                    return false;
                }

                return false;
            // NameSegment is someVar
            //  go through Ins & Outs of MemberDecl 
            //  make sure any with matching name are not ghost
            //  if you find a match, no need to check class fields
            //  else 
            //      go through all known fields of enclosing class,
            //      make sure any with matching name are not ghost
            } else if (expr is Microsoft.Dafny.NameSegment ns) {
                foreach (Microsoft.Dafny.Formal i in GetSigVars(st.MemberDeclFullDafnyName)) {
                    if (String.Equals(i.Name, ns.Name)) {
                        if (i.IsGhost) {
                            st.MarkInvalid();
                        } 
                        return false;
                    }
                }
                List<MemberDecl> memberList;
                classNameToGhostMemberMapper.TryGetValue(st.EnclosingClassFullName, out memberList);
                var res = memberList.OfType<Field>().SingleOrDefault(f => String.Equals(f.Name, ns.Name));
                if (res != null) {
                    st.MarkInvalid();
                }
                return false;
            }
            return true;
        }
    }

    public class EnsVisitorState {

        private bool state;
        private string enclosingClassFullName;
        private string memberDeclFullDafnyName;

        public bool State {
            get => state;
        }

        public string MemberDeclFullDafnyName {
            get => memberDeclFullDafnyName;
        }

        public string EnclosingClassFullName {
            get => enclosingClassFullName;
        }
        
        public EnsVisitorState(MemberDecl mDecl) {
            // save this to get Ins/Outs of MemberDecl being visited
            // is used as key to memberDeclNameToInsOutMapper
            memberDeclFullDafnyName = mDecl.FullDafnyName;
            // save this to get MemberList of Enclosing Class of MemberDecl being visited
            // is used as key to classNameToGhostMemberMapper
            enclosingClassFullName = mDecl.EnclosingClass.FullDafnyName;
            // is used to denote whether ensures expression is valid (allowed in expect stmt)
            state = true;
        }

        public void MarkInvalid() {
            state = false;
        }
    }
}