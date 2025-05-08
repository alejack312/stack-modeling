#lang forge
open "inheritance.frg"
open "root-and-hierarchy.frg"

test suite for hasNoParentClass {

    // Example: class has no parent (Positive)
    example testhasNoParentClassProper is {
        some c: SimpleClass | hasNoParentClass[c]
    } for {
        SimpleClass = `C
        AbstractClass = `C
        no `C.inherits
    }

    // Example: class inherits from itself (Negative)
    example testhasNoParentClassImproper is {
        no c: SimpleClass | hasNoParentClass[c]
    } for {
        SimpleClass = `C
        AbstractClass = `C
        `C.inherits = `C
    }

    // Assert: hasNoParentClass is satisfiable when a class has no parent
    testhasNoParentClassSat:
    assert some c: SimpleClass | hasNoParentClass[c]
        is sat for {
            SimpleClass = `C
            AbstractClass = `C
            no `C.inherits
        }

    // Assert: hasNoParentClass is unsatisfiable when all classes inherit
    testhasNoParentClassUnsat:
    assert some c: SimpleClass | hasNoParentClass[c]
        is unsat for {
            SimpleClass = `C
            AbstractClass = `C
            `C.inherits = `C
        }

    // Assert: no c.inherits is necessary for hasNoParentClass
    testHasNoParentClassNecessary:
    assert all c: SimpleClass | (
        no c.inherits
    ) is necessary for hasNoParentClass[c] for 2 SimpleClass, 2 AbstractClass

}

