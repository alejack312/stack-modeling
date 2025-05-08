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


// Helper predicate to check combine aggregation constraints with association and inheritance constraints as done in the implementation file
pred aggregationConstraintPredicates{
    associationConstraints and validAssociations and aggregationConstraints and inheritanceConstraints
}

test suite for aggregationConstraints {

    // Example: Valid interpretation of aggregationConstraints
    example testAggregationConstraintsProper is {
        aggregationConstraints
    } for {
        AbstractClass = `C1 + `C2
        SimpleClass = `C1 + `C2
        Association = `agg1 + `agg2
        Aggregation = `agg1 + `agg2

        `agg1.src = `C1
        `agg1.dst = `C2

        `agg2.src = `C1
        `agg2.dst = `C2
    }

    //Asserting aggregationConstraints is satisfiable, the source and destination of the aggregation are not reversed
    testAggregationSat: 
    assert aggregationConstraintPredicates is sat for 2 AbstractClass, 2 SimpleClass, 2 Association, 2 Aggregation
    

    // Example: InValid interpretation of aggregationConstraints
    example testAggregationConstraintsImproper is {
        not aggregationConstraints
    } for {
        AbstractClass = `C1 + `C2
        SimpleClass = `C1 + `C2
        Association = `agg1 + `agg2
        Aggregation = `agg1 + `agg2

        `agg1.src = `C1
        `agg1.dst = `C2

        `agg2.src = `C2
        `agg2.dst = `C1
    }


    //Asserting aggregationConstraints is unsatisfiable, the source and destination of the aggregation cannot be reversed
    testAggregationUnSat: 
    assert (some disj a1, a2: Aggregation| (
        a1.src = a2.dst and a2.src = a1.dst
    )) and aggregationConstraintPredicates is unsat for exactly 3 AbstractClass, 3 SimpleClass, exactly 2 Aggregation, exactly 2 Association

    //Example: A class in an aggregation relationship cannot ultimately reach itself

    example testAggregationConstraintsSelfReach is {
        not aggregationConstraints
    } for {
        AbstractClass = `C
        SimpleClass = `C
        Association = `agg1
        Aggregation = `agg1

        `agg1.src = `C
        `agg1.dst = `C
    }

    //Self reachability is unsatisfiable, the source and destination of the aggregation cannot be the same
    testSelfReachUnsat:
    assert (some a1: Aggregation| (
        a1.src = a1.dst
    )) and aggregationConstraintPredicates is unsat for exactly 3 AbstractClass, 3 SimpleClass, exactly 2 Aggregation, exactly 2 Association
}

// Helper predicate to check combine composition constraints with association and inheritance constraints as done in the implementation file

pred compositionConstraintPredicates { associationConstraints and validAssociations and compositionConstraints and inheritanceConstraints}

test suite for compositionConstraints {

    //Example: Valid interpretation of compositionConstraints -- destination uniqueness and exclusivity

    example destinationUniquenessProper is {
        compositionConstraints
    } for {
        AbstractClass = `C1 + `C2 + `C3 + `C4
        SimpleClass = `C1 + `C2 + `C3 + `C4
        Association = `comp1_C1_C2 + `comp2_C3_C4
        Composition = `comp1_C1_C2 + `comp2_C3_C4

        `comp1_C1_C2.src = `C1
        `comp1_C1_C2.dst = `C2

        `comp2_C3_C4.src = `C3
        `comp2_C3_C4.dst = `C4
        
        }
    
    //Asserting conposition constraints are satisfiable, no mutual compositions, no cycles.
    testCompositionSat: 
    assert aggregationConstraintPredicates is sat for 2 AbstractClass, 2 SimpleClass, 2 Association, 2 Aggregation

    //Example: invalid interpretation of compositionConstraints -- destination uniqueness and exclusivity C3 is destination of two compositions (from C1 and C2)

    example destinationUniquenessImproper is {
        not compositionConstraints
    } for {
        AbstractClass = `C1 + `C2 + `C3
        SimpleClass = `C1 + `C2 + `C3
        Association = `comp1_C1_C3 + `comp2_C2_C3
        Composition = `comp1_C1_C3 + `comp2_C2_C3

        `comp1_C1_C3.src = `C1
        `comp1_C1_C3.dst = `C3

        `comp2_C2_C3.src = `C2
        `comp2_C2_C3.dst = `C3
    }

    //Asserting aggregationConstraints is unsatisfiable, the destination of two compositions cannot be the same 
    destinationUnSat: 
    assert (some disj c1, c2: Composition| (
        c1.dst = c2.dst and c2.src != c1.src
    )) and compositionConstraintPredicates is unsat for exactly 3 AbstractClass, exactly 3 SimpleClass, exactly 2 Aggregation

    // Example: Invalid - Mutual composition (C1 composes C2, C2 composes C1)
    example testCompositionConstraintsImproper_MutualComposition is {
        not compositionConstraints
    } for {
        AbstractClass = `C1 + `C2
        SimpleClass = `C1 + `C2
        Association = `comp1_C1_C2 + `comp2_C2_C1
        Composition = `comp1_C1_C2 + `comp2_C2_C1

        `comp1_C1_C2.src = `C1
        `comp1_C1_C2.dst = `C2

        `comp2_C2_C1.src = `C2
        `comp2_C2_C1.dst = `C1
    }

    //Asserting aggregationConstraints is unsatisfiable, the destination of two compositions cannot be the same 
    mutualityUnSat: 
    assert (some disj c1, c2: Composition| (
        c1.src = c2 and c2.src = c1 and c1.dst = c2 and c2.dst = c1
    )) and compositionConstraintPredicates is unsat for exactly 3 AbstractClass, exactly 3 SimpleClass, exactly 2 Aggregation

    // Example: Invalid - Composition cycle (C1 -> C2 -> C3 -> C1)
    example testCompositionConstraintsacyclicle is {
        not compositionConstraints
    } for {
        AbstractClass = `C1 + `C2 + `C3
        SimpleClass = `C1 + `C2 + `C3
        Association = `comp1_C1_C2 + `comp2_C2_C3 + `comp3_C3_C1
        Composition = `comp1_C1_C2 + `comp2_C2_C3 + `comp3_C3_C1

        `comp1_C1_C2.src = `C1
        `comp1_C1_C2.dst = `C2

        `comp2_C2_C3.src = `C2
        `comp2_C2_C3.dst = `C3

        `comp3_C3_C1.src = `C3
        `comp3_C3_C1.dst = `C1
    }

    // Asserting that the existence of a composition cycle is unsatisfiable when compositionConstraintPredicates must hold
    cyclicityUnSat: 
    assert (some c: AbstractClass | c in c.^(Composition.src->Composition.dst))
        and compositionConstraintPredicates is unsat for exactly 3 AbstractClass, exactly 3 SimpleClass, exactly 3 Association, exactly 3 Composition

}
