#lang forge

open "main.frg"

// Any chosen stack must be fully pairwise compatible
// Any chosen stack must be fully pairwise compatible
assert FullStackCompatible {
  all f: Frontend, b: Backend, d: Database, o: ORM, a: Authorization | {
    (some c: Compatibility | c.tech1 = f and c.tech2 = b and c.compatible = True) and
    (some c: Compatibility | c.tech1 = f and c.tech2 = d and c.compatible = True) and
    (some c: Compatibility | c.tech1 = f and c.tech2 = o and c.compatible = True) and
    (some c: Compatibility | c.tech1 = f and c.tech2 = a and c.compatible = True) and
    (some c: Compatibility | c.tech1 = b and c.tech2 = d and c.compatible = True) and
    (some c: Compatibility | c.tech1 = b and c.tech2 = o and c.compatible = True) and
    (some c: Compatibility | c.tech1 = b and c.tech2 = a and c.compatible = True) and
    (some c: Compatibility | c.tech1 = d and c.tech2 = o and c.compatible = True) and
    (some c: Compatibility | c.tech1 = d and c.tech2 = a and c.compatible = True) and
    (some c: Compatibility | c.tech1 = o and c.tech2 = a and c.compatible = True)
  }
}

// check FullStackCompatible for 5 Tech, 20 Compatibility