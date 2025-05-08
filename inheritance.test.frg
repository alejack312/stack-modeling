#lang forge

open "inheritance.frg" // Import the inheritance model


test suite for noSelfInheritance {
    // No class should inherit from itself
    assert {no c: AbstractClass | c in c.inherits} is sat
}

test suite for inheritanceModel {
    // 1. Nontrivial hierarchy exists (at least one class with a parent)
    assert {some c: AbstractClass | #c.inherits > 0} is sat

    // 2. No class can inherit from itself (directly or indirectly)
    assert {no c: AbstractClass | c in c.^inherits} is sat

    // 3. No redundant inheritance: removing a direct grandparent edge does not break reachability
    assert {no c, p, a: AbstractClass | p in c.inherits and a in p.^inherits and a in c.inherits} is sat

    // 4. Inheritance is not symmetric
    assert {no c1, c2: AbstractClass | c1 in c2.inherits and c2 in c1.inherits} is sat

    // 5. Multiple roots are possible
    assert {some disj c1, c2: AbstractClass | no c1.inherits and no c2.inherits} is sat

    // 6. Interface can be unimplemented
    assert {some i: Interface | no c: AbstractClass | i in c.implements} is sat

    // 7. Class can exist without implementing any interface
    assert {some c: AbstractClass | no i: Interface | i in c.implements} is sat

    // 8. Class cannot implement the same interface as an ancestor
    assert {
        no c: AbstractClass, i: Interface | i in c.implements and 
        (some p: c.^inherits | i in p.implements)
    } is sat

    // 11. Hierarchy can be deeper than two levels
    assert {some c, p, a: AbstractClass | p in c.inherits and a in p.inherits} is sat

    // 12. Resolution policy: RequireOverride enforces explicit override
    assert { 
        no c: ExtendedClass | c.policy = RequireOverride and 
        (some p1, p2: c.inherits | {
            p1 != p2 and 
            (some m: Method | {
                m in p1.methodsC and m in p2.methodsC and m not in c.methodsC
            })
        })  
    } is sat

    // 13. Resolution policy: MergeAll includes all parent methods
    assert { 
        no c: ExtendedClass | c.policy = MergeAll and 
        (some p: c.inherits, m: Method | m in p.methodsC and m not in c.methodsC)
    } is sat

    // 14. Non-vacuity: model admits at least one nontrivial instance
    assert {some c: AbstractClass, p: AbstractClass | p in c.inherits} is sat

    // 15. Example: a class with two parents (multiple inheritance)
    example twoParents is {multipleInheritance} for {
        AbstractClass = `C0 + `C1 + `C2
        ExtendedClass = `C0 + `C1 + `C2
        Interface = `I0
        Method = `M0
        Field = `F0
        ResolutionPolicy = `LeftWins + `RightWins + `RequireOverride + `MergeAll
        LeftWins = `LeftWins
        RightWins = `RightWins
        RequireOverride = `RequireOverride
        MergeAll = `MergeAll
        `C0.inherits = `C1 + `C2
        no `C0.implements
        no `C1.inherits
        no `C2.inherits
        no `C0.methodsC
        no `C1.methodsC
        no `C2.methodsC
        no `C0.fieldsC
        no `C1.fieldsC
        no `C2.fieldsC
        `C0.policy = `LeftWins
        `C1.policy = `LeftWins
        `C2.policy = `LeftWins
        no `C0.parentOrder
        no `C1.parentOrder
        no `C2.parentOrder

        no `C1.implements
        no `C2.implements
        no `I0.methodsI
        no `I0.fieldsI
    }

    // Example: single inheritance (C0 inherits C1)
    example singleInheritanceExample is {singleInheritance} for {
        AbstractClass = `C0 + `C1
        ExtendedClass = `C0 + `C1
        Interface = `I0
        Method = `M0
        Field = `F0
        ResolutionPolicy = `LeftWins + `RightWins + `RequireOverride + `MergeAll
        LeftWins = `LeftWins
        RightWins = `RightWins
        RequireOverride = `RequireOverride
        MergeAll = `MergeAll
        `C0.inherits = `C1
        no `C1.inherits
        no `C0.implements
        no `C1.implements
        no `C0.methodsC
        no `C1.methodsC
        no `C0.fieldsC
        no `C1.fieldsC
        `C0.policy = `LeftWins
        `C1.policy = `LeftWins
        no `C0.parentOrder
        no `C1.parentOrder
        no `I0.methodsI
        no `I0.fieldsI
    }

    // Example: class implements interface
    example implementsInterface is { generalization } for {
        AbstractClass = `C0 + `C1
        ExtendedClass = `C0 + `C1
        Interface = `I0
        Method = `M0
        Field = `F0
        ResolutionPolicy = `LeftWins + `RightWins + `RequireOverride + `MergeAll
        LeftWins = `LeftWins
        RightWins = `RightWins
        RequireOverride = `RequireOverride
        MergeAll = `MergeAll
        `C0.inherits = `C1
        no `C1.inherits
        `C0.implements = `I0
        no `C1.implements
        no `C0.methodsC
        no `C1.methodsC
        no `C0.fieldsC
        no `C1.fieldsC
        `C0.policy = `LeftWins
        `C1.policy = `LeftWins
        no `C0.parentOrder
        no `C1.parentOrder
        `I0.methodsI = `M0
        no `I0.fieldsI
    }

    // Example: deeper hierarchy (C0 inherits C1, C1 inherits C2)
    example deepHierarchy is { generalization } for {
        AbstractClass = `C0 + `C1 + `C2
        ExtendedClass = `C0 + `C1 + `C2
        Interface = `I0
        Method = `M0
        Field = `F0
        ResolutionPolicy = `LeftWins + `RightWins + `RequireOverride + `MergeAll
        LeftWins = `LeftWins
        RightWins = `RightWins
        RequireOverride = `RequireOverride
        MergeAll = `MergeAll
        `C0.inherits = `C1
        `C1.inherits = `C2
        no `C2.inherits
        no `C0.implements
        no `C1.implements
        no `C2.implements
        no `C0.methodsC
        no `C1.methodsC
        no `C2.methodsC
        no `C0.fieldsC
        no `C1.fieldsC
        no `C2.fieldsC
        `C0.policy = `LeftWins
        `C1.policy = `LeftWins
        `C2.policy = `LeftWins
        no `C0.parentOrder
        no `C1.parentOrder
        no `C2.parentOrder
        no `I0.methodsI
        no `I0.fieldsI
    }
}

test suite for singleInheritance {
    // 9. Single inheritance: at most one parent
    assert {all c: AbstractClass | #c.inherits <= 1} is sat for 5 AbstractClass // but singleInheritance
}

test suite for multipleInheritance {
    // 10. Multiple inheritance: more than one parent possible
    assert {some c: AbstractClass | #c.inherits > 1} is sat for 5 AbstractClass // but multipleInheritance
}
