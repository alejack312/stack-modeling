#lang forge
open "inheritance.frg"
open "associativity-multiplicity.frg"

test suite for noSelfAssociation {

    // Example: every association has distinct src and dst (Positive)
    example testNoSelfAssociationProper is { 
        all a: Association | noSelfAssociation
    } for {
        AbstractClass = `C1 + `C2
        SimpleClass = `C1 + `C2
        Association = `a
        `a.src = `C1
        `a.dst = `C2
    }

    // Example: at least one association has src = dst (Negative)
    example testNoSelfAssociationImproper is { 
        all a: Association | not noSelfAssociation
    } for {
        AbstractClass = `C
        SimpleClass = `C
        Association = `a
        `a.src = `C
        `a.dst = `C
    }

    // Assert: src != dst is necessary for noSelfAssociation
    testNoSelfAssociationAssert: assert all a: Association | (a.src != a.dst) is necessary for noSelfAssociation for 2 SimpleClass, 1 Association
}

test suite for noInterfaceToInterfaceAssociation {

    // Example: associations connect two Classes
    example testNoInterfaceToInterfaceAssociationProper is { 
        all a: Association | noInterfaceToInterfaceAssociation
    } for {
        AbstractClass = `C1 + `C2
        SimpleClass = `C1 + `C2
        Association = `a
        `a.src = `C1
        `a.dst = `C2
    }

    // Assert: there is no instance where either the src or dst are Interfaces
    testNoInterfaceToInterfaceAssociationUnsat1: assert some a: Association | (a.src in Interface or a.dst in Interface) is unsat

    // Assert: there is no instance where the src and dst are Interfaces
    testNoInterfaceToInterfaceAssociationUnsat2: assert some a: Association | (a.src in Interface and a.dst in Interface) is unsat

    // Assert: not (a.src in Interface and a.dst in Interface) is necessary for noInterfaceToInterfaceAssociation
    testNoInterfaceToInterfaceAssociationNecessary: assert all a: Association | not (a.src in Interface and a.dst in Interface) is necessary for noInterfaceToInterfaceAssociation for 2 Interface, 1 Association
}

test suite for noRedundantAssociationAtoms {

    // Example: two associations with distinct src–dst pairs (Positive)
    example testNoRedundantAssociationAtomsProper is {
        noRedundantAssociationAtoms
    } for {
        AbstractClass = `C1 + `C2
        SimpleClass = `C1 + `C2
        Association = `a1 + `a2

        `a1.src = `C1
        `a1.dst = `C2

        `a2.src = `C2
        `a2.dst = `C1
    }

    // Example: two associations with the same src–dst pair (Negative)
    example testNoRedundantAssociationAtomsImproper is {
        not noRedundantAssociationAtoms
    } for {
        AbstractClass = `C1 + `C2
        SimpleClass = `C1 + `C2
        Association = `a1 + `a2

        `a1.src = `C1
        `a1.dst = `C2
        `a2.src = `C1
        `a2.dst = `C2
    }

    // Assert: the predicate is satisfiable when there are no redundant atoms
    testNoRedundantSat:
    assert noRedundantAssociationAtoms is sat for 2 SimpleClass, 2 Association

    // Assert: parallel edges are impossible under the predicate
    testNoRedundantUnsat:
    assert some disj a1, a2: Association | (a1.src = a2.src and a1.dst = a2.dst) and noRedundantAssociationAtoms is unsat for 2 SimpleClass, 2 Association

    // Assert: absence of parallel edges is necessary for the predicate
    testNoRedundantNecessary:
    assert all disj a1, a2: Association | not (a1.src = a2.src and a1.dst = a2.dst)
        is necessary for noRedundantAssociationAtoms
        for 2 SimpleClass, 2 Association
}

test suite for associationConstraints {

    // Example: both interface‐check and redundancy‐check pass (Positive)
    example testAssociationConstraintsProper is {
        associationConstraints
    } for {
        AbstractClass = `C1 + `C2
        SimpleClass = `C1 + `C2
        Association = `a1 + `a2

        `a1.src = `C1
        `a1.dst = `C2
        `a2.src = `C2
        `a2.dst = `C1
    }

    // Example: redundancy violation only (interfaces remain Classes) (Negative)
    example testAssociationConstraintsRedundantImproper is {
        not associationConstraints
    } for {
        AbstractClass = `C1 + `C2
        SimpleClass = `C1 + `C2
        Association = `a1 + `a2

        `a1.src = `C1
        `a1.dst = `C2
        `a2.src = `C1
        `a2.dst = `C2
    }

    // Assert: you can never have an interface‐to‐interface association
    testAssociationConstraintsInterfaceUnsat:
    assert some a: Association | (a.src in Interface and a.dst in Interface)
        is unsat for 2 Interface, 1 Association

    // Assert: you can never have an interface‐to‐interface association even if there are no redundant associations
    testAssociationConstraintsInterfaceWithoutRedundancyUnsat:
    assert some a: Association |
           (a.src in Interface and a.dst in Interface)
        and (all disj a1, a2: Association | not (a1.src = a2.src and a1.dst = a2.dst))
        is unsat for 2 Interface, 1 Association

    // Assert: you cannot simultaneously have an interface‐to‐interface association and a parallel edge
    testAssociationConstraintsBothUnsat:
    assert some disj a1, a2: Association |
           (a1.src in Interface and a1.dst in Interface)
        and (a1.src = a2.src and a1.dst = a2.dst)
        is unsat for 2 Interface, 2 Association

    // Assert: no interfaces is necessary for associationConstraints
    testAssociationConstraintsInterfaceNecessary:
    assert all a: Association | not (a.src in Interface and a.dst in Interface)
        is necessary for associationConstraints
        for 2 Interface, 1 Association

    // Assert: no redundancy is necessary for associationConstraints
    testAssociationConstraintsRedundantNecessary:
    assert all disj a1, a2: Association | not (
        a1.src = a2.src and a1.dst = a2.dst
    ) is necessary for associationConstraints
        for 2 SimpleClass, 2 Association
}

test suite for validAssociations {

    // Example: every association has distinct src and dst, i.e. src != dst (Positive)
    example testValidAssociationsProper is {
        validAssociations
    } for {
        AbstractClass = `C1 + `C2
        SimpleClass = `C1 + `C2
        Association = `a
        `a.src = `C1
        `a.dst = `C2
    }

    // Example: an association has src = dst (Negative)
    example testValidAssociationsImproper is {
        not validAssociations
    } for {
        AbstractClass = `C
        SimpleClass = `C
        Association = `a
        `a.src = `C
        `a.dst = `C
    }

    // Assert: validAssociations is satisfiable when all src != dst
    testValidAssociationsSat:
    assert validAssociations is sat for 2 SimpleClass, 1 Association

    // Assert: src != dst is necessary for validAssociations
    testValidAssociationsNecessary:
    assert all a: Association | (a.src != a.dst)
        is necessary for validAssociations
        for 2 SimpleClass, 1 Association
}