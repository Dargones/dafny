// RUN: %verify --relax-definite-assignment --unicode-char false "%s" > "%t"
// RUN: %exits-with 3 %run --no-verify --unicode-char false --target cs "%s" >> "%t"
// RUN: %exits-with 3 %run --no-verify --unicode-char false --target java "%s" >> "%t"
// RUN: %exits-with 3 %run --no-verify --unicode-char false --target js "%s" >> "%t"
// RUN: %exits-with 3 %run --no-verify --unicode-char false --target go "%s" >> "%t"
// RUN: %exits-with 3 %run --no-verify --unicode-char false --target cpp "%s" >> "%t"
// RUN: %exits-with 3 %run --no-verify --unicode-char false --target py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

// The following example should produce a compilation error, since there's
// an abstract type. It should not, however, crash.

type Opaque(0) // compilation error: this is an abstract type

datatype E = E(Opaque)

method N() returns (e: E) {
}

method Main() {
  var e := N();
  print e, "\n";
}
