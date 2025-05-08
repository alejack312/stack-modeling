#lang forge

open "associativity-multiplicity.frg"
open "inheritance.frg" // Import the inheritance model

test suite for noSelfAssociation {

    // Example: every association has distinct src and dst (Positive)
    example testNoSelfAssociationProper is { 
        all a: Association | noSelfAssociation
    } for {
        Class = `C1 + `C2
        Association = `a
        `a.src = `C1
        `a.dst = `C2
    }

    // Example: at least one association has src = dst (Negative)
    example testNoSelfAssociationImproper is { 
        all a: Association | not noSelfAssociation
    } for {
        Class = `C
        Association = `a
        `a.src = `C
        `a.dst = `C
    }

    // Assert: src != dst is necessary for noSelfAssociation
    testNoSelfAssociationAssert: assert all a: Association | (a.src != a.dst) is necessary for noSelfAssociation for 2 Class, 1 Association
}

test suite for noInterfaceToInterfaceAssociation {

    // Example: associations connect two Classes
    example testNoInterfaceToInterfaceAssociationProper is { 
        all a: Association | noInterfaceToInterfaceAssociation
    } for {
        Class = `C1 + `C2
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
        Class = `C1 + `C2
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
        Class = `C1 + `C2
        Association = `a1 + `a2

        `a1.src = `C1
        `a1.dst = `C2
        `a2.src = `C1
        `a2.dst = `C2
    }

    // Assert: the predicate is satisfiable when there are no redundant atoms
    testNoRedundantSat:
    assert noRedundantAssociationAtoms is sat for 2 Class, 2 Association

    // Assert: parallel edges are impossible under the predicate
    testNoRedundantUnsat:
    assert some disj a1, a2: Association | (a1.src = a2.src and a1.dst = a2.dst) and noRedundantAssociationAtoms is unsat for 2 Class, 2 Association

    // Assert: absence of parallel edges is necessary for the predicate
    testNoRedundantNecessary:
    assert all disj a1, a2: Association | not (a1.src = a2.src and a1.dst = a2.dst)
        is necessary for noRedundantAssociationAtoms
        for 2 Class, 2 Association
}

test suite for associationConstraints {

    // Example: both interface‐check and redundancy‐check pass (Positive)
    example testAssociationConstraintsProper is {
        associationConstraints
    } for {
        Class = `C1 + `C2
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
        Class = `C1 + `C2
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
        for 2 Class, 2 Association
}

test suite for validAssociations {

    // Example: every association has distinct src and dst, i.e. src != dst (Positive)
    example testValidAssociationsProper is {
        validAssociations
    } for {
        Class = `C1 + `C2
        Association = `a
        `a.src = `C1
        `a.dst = `C2
    }

    // Example: an association has src = dst (Negative)
    example testValidAssociationsImproper is {
        not validAssociations
    } for {
        Class = `C
        Association = `a
        `a.src = `C
        `a.dst = `C
    }

    // Assert: validAssociations is satisfiable when all src != dst
    testValidAssociationsSat:
    assert validAssociations is sat for 2 Class, 1 Association

    // Assert: src != dst is necessary for validAssociations
    testValidAssociationsNecessary:
    assert all a: Association | (a.src != a.dst)
        is necessary for validAssociations
        for 2 Class, 1 Association
}

pred constraintPredicates{
        associationConstraints and validAssociations and aggregationConstraints and inheritanceConstraints
    }

test suite for aggregationConstraints {

    // Example: Valid interpretation of aggregationConstraints
    example testAggregationConstraintsProper is {
        aggregationConstraints
    } for {
        Class = `C1 + `C2
        Association = `agg1 + `agg2
        Aggregation = `agg1 + `agg2

        `agg1.src = `C1
        `agg1.dst = `C2

        `agg2.src = `C1
        `agg2.dst = `C2
    }

    //Asserting aggregationConstraints is satisfiable, the source and destination of the aggregation are not reversed
    testAgggregationUnSat: 
    assert aggregationConstraints is unsat for 2 Class, 2 Association, 2 Aggregation
    

    // Example: InValid interpretation of aggregationConstraints
    example testAggregationConstraintsImproper is {
        aggregationConstraints
    } for {
        Class = `C1 + `C2
        Association = `agg1 + `agg2
        Aggregation = `agg1 + `agg2

        `agg1.src = `C1
        `agg1.dst = `C2

        `agg2.src = `C2
        `agg2.dst = `C1
    }


    //Asserting aggregationConstraints is unsatisfiable, the source and destination of the aggregation cannot be reversed
    testAgggregationUnSat: 
    assert all disj a1, a2: Aggregation| not (
        a1.src = a2.dst and a2.src = a1.dst
    ) is necessary for constraintPredicates for exactly 3 Class, exactly 2 Aggregation, exactly 2 Association

    //Example: A class in an aggregation relationship cannot ultimately reach itself

    example testAggregationConstraintsSelfReach is {
        aggregationConstraints
    } for {
        Class = `C
        Association = `agg1
        Aggregation = `agg1

        `agg1.src = `C
        `agg1.dst = `C
    }

    //Self reachability is unsatisfiable, the source and destination of the aggregation cannot be the same
    testSelfReachUnsat:
    assert aggregationConstraints is unsat for 2 Class, 1 Association, 1 Aggregation
}

