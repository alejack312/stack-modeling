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
    ) is necessary for hasNoParentClass[c] for exactly 2 SimpleClass, exactly 2 AbstractClass

    // Assert: no c.inherits is sufficient for hasNoParentClass
    testHasNoParentClassSufficient:
    assert all c: SimpleClass | (
        no c.inherits
    ) is sufficient for hasNoParentClass[c] for exactly 2 SimpleClass, exactly 2 AbstractClass
}

test suite for rootConnectivity {

    // Example: one class with no parent is connected to Root (Positive)
    example testRootConnectivityProper1 is {
        rootConnectivity
    } for {
        SimpleClass = `C
        AbstractClass = `C
        Root = `R
        no `C.inherits
        no `C.implements
        `R.topLevelClasses = `C
    }

    // Example: two classes where C1 is top‐level and C2 descends from C1 (Positive)
    example testRootConnectivityProper2 is {
        rootConnectivity
    } for {
        SimpleClass = `C1 + `C2
        AbstractClass = `C1 + `C2
        Root = `R
        no `C1.inherits
        `C2.inherits = `C1
        no `C1.implements
        no `C2.implements
        `R.topLevelClasses = `C1
    }

    // Example: one class with no parent is not in Root.topLevelClasses (Negative)
    example testRootConnectivityImproper1 is {
        not rootConnectivity
    } for {
        SimpleClass = `C
        AbstractClass = `C
        Root = `R
        no `C.inherits
        no `C.implements
        no `R.topLevelClasses
    }

    // Example: one class is in Root.topLevelClasses but has a parent (Negative)
    example testRootConnectivityImproper2 is {
        not rootConnectivity
    } for {
        SimpleClass = `C1 + `C2
        AbstractClass = `C1 + `C2
        Root = `R
        `C2.inherits = `C1
        `R.topLevelClasses = `C2
        no `C1.inherits
        no `C1.implements
        no `C2.implements
    }

    // Example: class has no parent and is not in Root.topLevelClasses, and a different class is in topLevelClasses but has a parent (Negative)
    example testRootConnectivityImproper3 is {
        not rootConnectivity
    } for {
        SimpleClass = `C1 + `C2
        AbstractClass = `C1 + `C2
        Root = `R
        no `C1.inherits
        `C2.inherits = `C1
        `R.topLevelClasses = `C2
        no `C1.implements
        no `C2.implements
    }

    // Assert: rootConnectivity is sat when every parentless class is in Root.topLevelClasses and vice versa
    rootConnectivitySat: assert {
        rootConnectivity and (
            all c: SimpleClass | (
                hasNoParentClass[c] iff c in Root.topLevelClasses
            )
        )
    } is sat for exactly 2 SimpleClass, exactly 1 Root

    // Assert: a violation of rootConnectivity with a parentless class not in Root.topLevelClasses is unsat
    rootConnectivityUnsat1: assert {
        rootConnectivity and (
            some c: SimpleClass | hasNoParentClass[c] and c not in Root.topLevelClasses
        )
    } is unsat for exactly 2 SimpleClass, exactly 1 Root

    // Assert: a violation of rootConnectivity with a class in Root.topLevelClasses that has a parent is unsat
    rootConnectivityUnsat2: assert {
        rootConnectivity and (
            some c: SimpleClass | c in Root.topLevelClasses and not hasNoParentClass[c]
        )
    } is unsat for exactly 2 SimpleClass, exactly 1 Root
}

test suite for rootAndHierarchyIntegrity {

    // Example: simple, well‐formed hierarchy (Positive)
    example testRootAndHierarchyProper is {
        rootAndHierarchyIntegrity
    } for {
        SimpleClass = `C1 + `C2
        AbstractClass = `C1 + `C2
        Root = `R
        no  `C1.inherits
        `C2.inherits = `C1
        no `C1.implements
        no `C2.implements
        `R.topLevelClasses = `C1
    }

    // Example: self‐inheritance violates inheritanceConstraints (Negative)
    example testRootAndHierarchyImproperInheritance is {
        not rootAndHierarchyIntegrity
    } for {
        SimpleClass = `C
        AbstractClass = `C
        Root = `R
        `C.inherits = `C
        no `C.implements
        no `R.topLevelClasses
    }

    // Example: a class with two parents breaks the (single ∨ multiple)‐inheritance clause (Negative)
    example testRootAndHierarchyImproperMultiplicity is {
        not rootAndHierarchyIntegrity
    } for {
        SimpleClass = `C0 + `C1 + `C2
        AbstractClass = `C0 + `C1 + `C2
        Root = `R
        `C0.inherits = `C1 + `C2
        no `C0.implements
        no `C1.implements
        no `C2.implements
        no `R.topLevelClasses
    }

    // Example: parentless class not in Root.topLevelClasses breaks rootConnectivity (Negative)
    example testRootAndHierarchyImproperRoot is {
        not rootAndHierarchyIntegrity
    } for {
        SimpleClass = `C
        AbstractClass = `C
        Root = `R
        no `C.inherits
        no `C.implements
        no `R.topLevelClasses
    }

    // Assert: you can’t satisfy rootAndHierarchyIntegrity if inheritanceConstraints fails
    rootAndHierarchyUnsatInheritance:
    assert {
        rootAndHierarchyIntegrity and (some c: AbstractClass | c in c.inherits)
    } is unsat for exactly 1 SimpleClass, exactly 1 AbstractClass, exactly 1 Root

    // Assert: you can satisfy rootAndHierarchyIntegrity if a class has two parents since single and multi inheritance are permitted
    rootAndHierarchySatMultiplicity:
    assert {
        rootAndHierarchyIntegrity and (some c: AbstractClass | #c.inherits > 1)
    } is sat for exactly 3 SimpleClass, exactly 3 AbstractClass, exactly 1 Root

    // Assert: you can’t satisfy rootAndHierarchyIntegrity if a parentless class isn’t in the root
    rootAndHierarchyUnsatRoot:
    assert {
        rootAndHierarchyIntegrity and (some c: SimpleClass | hasNoParentClass[c] and c not in Root.topLevelClasses)
    } is unsat for exactly 2 SimpleClass, exactly 2 AbstractClass, exactly 1 Root
}