#lang forge

open "inheritance.frg" // Import the inheritance model

// =============================================================================
// Association and Multiplicity Constraints
// =============================================================================



sig Association {
    src: one AbstractClass,    // Source of the relationship
    dst: one AbstractClass   // Destination of the relationship
}

sig Aggregation extends Association {
    // Aggregation implies a relationship where the child can exist independently of the parent.
} 

sig Composition extends Association {
    // Composition implies a relationship where the child cannot exist independent of the parent.



} // Define Aggregation and Composition as subtypes of Association

// Valid Association Types


// Predicate to prevent self-associations
pred noSelfAssociation {
    no a: Association | a.src = a.dst
}

// Predicate to prevent direct Interface-to-Interface associations
pred noInterfaceToInterfaceAssociation {
    no a: Association | a.src in Interface and a.dst in Interface
}

// Predicate to prevent fully redundant association atoms
pred noRedundantAssociationAtoms {
    all disj a1, a2: Association | not (
        a1.src = a2.src and
        a1.dst = a2.dst
    )
}

/*
    Production 4: Association Constraints

    Validates that associations between classes are structurally well-formed, i.e. no direct
    associations between 2 Interface nodes and no 2 distinct Association instances connect the
    same pair of classes in the same direction (aka no parallel/redundant association edges)

    NOTE: Does not specify the type of association that is permitted, i.e. standard/valid or 
    reflexive, which are handled by Production 7 and Production 14, respectively.
*/
pred associationConstraints { 
    noInterfaceToInterfaceAssociation and noRedundantAssociationAtoms

    
    /*
        Add a check that asserts that two Associations do not have the same source and destination.
        This is to prevent redundant association atoms. (this is covered by validAssociations already)

        Check to see if a Association can have its source be one class 
        and its destination be the child of that class. (yes, since this is not specified by definition for associations
        and is covered by acyclicity clauses for aggregations and compositions)
    */
}

/*
    Production 7: Standard Association

    Given an association, the source and destination of the association must be different classes.
*/
pred validAssociations {
    all a: Association | {
        // The source and destination of the association must be different classes
        (a.src != a.dst)
    }
}

/*
    NOTE: If the number of the number of classes divided by the number of association modulo 2 is not equal to 0, 
    then we need to ensure that a class does not have more than one association.
*/
runValidAssociations : run { validAssociations and associationConstraints and inheritanceConstraints} for exactly 2 SimpleClass, exactly 1 Association, exactly 2 AbstractClass, exactly 0 Interface // Run the model for 3 classes and 2 associations


/*
    Production 8: Aggregation
*/
pred aggregationConstraints {
    no disj agg1, agg2: Aggregation | {
        // Aggregation relationships cannot be mutual such that the relationship can
        // be directly reversed to form another aggregation relationship, i.e. if A "has"
        // B, then it cannot be true that B "has" A
        (agg1.src = agg2.dst) and (agg2.src = agg1.dst)
    }
    no c: AbstractClass | {

        // A class in an aggregation relationship cannot ultimately reach itself
        c in c.^(Aggregation.src->Aggregation.dst)
    }
}

runValidAggregation : run { associationConstraints and validAssociations and aggregationConstraints and inheritanceConstraints} for exactly 3 AbstractClass, exactly 3 SimpleClass, exactly 2 Aggregation, exactly 2 Association, exactly 0 Interface // Run the model for 3 classes and 2 associations

/*
    Production 9: Composition
*/
pred compositionConstraints {
    all cl: AbstractClass | {
        // if a class is a destination in any composition relationship, it must be the 
        // destination of exactly one composition and may not be the destination of an aggregation
        (some comp: Composition | comp.dst = cl) implies (
            (one comp: Composition | comp.dst = cl) and
            (no agg: Aggregation | agg.dst = cl)
        )
    }
    no disj comp1, comp2: Composition | {
        // Composition relationships cannot be mutual such that the relationship can
        // be directly reversed to form another composition relationship, i.e. if A "owns"
        // B, then it cannot be true that B "owns" A
        (comp1.src = comp2.dst) and (comp2.src = comp1.dst)
    }
    no c: AbstractClass | {
        // A class in a composition relationship cannot ultimately reach itself
        c in c.^(Composition.src->Composition.dst)
    }
}

runValidComposition : run { associationConstraints and validAssociations and compositionConstraints and inheritanceConstraints} for exactly 3 AbstractClass, exactly 3 SimpleClass, exactly 2 Composition, exactly 2 Association, exactly 0 Interface // Run the model for 3 classes and 2 associations

/*
    No overlap between Aggregation and Composition regardless of direction since Aggregation
    implies that the part/destination class can exist independently whereas a Composition
    implies the opposite.
*/
pred noAggregationCompositionOverlap {
    // No Aggregation and Composition may have the same src and dst Classes
    all agg: Aggregation, comp: Composition | {
        not (agg.src = comp.src and agg.dst = comp.dst)
    }
    // No Aggregation and Composition may have opposite/flipped src and dst Classes
    all agg: Aggregation, comp: Composition | {
        not (agg.src = comp.dst and agg.dst = comp.src)
    }
}

runNoAggregationCompositionOverlap: run { associationConstraints and validAssociations and aggregationConstraints and compositionConstraints and inheritanceConstraints and noAggregationCompositionOverlap} for exactly 5 SimpleClass, exactly 5 AbstractClass, exactly 2 Composition, exactly 2 Aggregation, exactly 5 Association, exactly 0 Interface


/*
    We need to assert at the very least that an Aggregation relationship and 
    a Composition relationship do NOT share the same source and destination.

    Verify is it is possible or not to have two classes hold an Aggregation
    and Composition relationship when the source and destination of the two are
    flipped.
*/

/*
    Production 14: Reflective Association

    Given an association, the source and destination of the association must be the same class.

    NOTE: This constraint does not make much semantic sense for Aggregation or Composition relationships,
    as a class can neither contain itself (with itself being able to exist independently of itself) as in
    an Aggregation, nor can a class own itself as in a Composition.
*/
pred reflectiveAssociations {
    // An association must be reflexive, meaning that it can be traversed in both directions.
    
    all a : Association | {
        // The source and destination of the association must be the same class
        (a.src = a.dst)
    }
}

// This is using Aggregation and Composition as well as Association. This is 

reflectiveAssociationsRun : run { reflectiveAssociations and associationConstraints and inheritanceConstraints} for exactly 1 SimpleClass, exactly 1 AbstractClass, exactly 1 Association, exactly 0 Interface  // Run the model for 1 class and 1 association 

