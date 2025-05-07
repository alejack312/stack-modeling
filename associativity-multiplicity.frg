#lang forge

// =============================================================================
// Interfaces
// =============================================================================



sig Interface {
    implementer : one Class
} // Define Interface signature



/*
    Production 6: One Interface per Class

    To TEST:
    A graph specifying structure is invalid if it breaks at least one relationship
    specified in any production. For example, Production 6 in Figure 3 define one 
    interface can only attach to one class. If an interface is designed to be 
    related to more than one class, a parser can indicate a violation of 
    Production 6. 

*/
pred interfaceMultiplicity {
    all i: Interface | some i.implementer  
}

runInterfaceMultiplicity : run { interfaceMultiplicity and inheritanceConstraints } for 2 Class, 1 Interface // Run the model for 2 classes and 1 interface

runGeneralization : run generalization for 5 Class // Run the model for 5 classes






// =============================================================================
// Association and Multiplicity Constraints
// =============================================================================


sig Association {
    src: one Class,    // Source of the relationship
    dst: one Class   // Destination of the relationship
}

sig Aggregation extends Association {
    // Aggregation implies a relationship where the child can exist independently
    // of the parent.
} 

sig Composition extends Association {
    // Composition implies a relationship where the child cannot exist 
    // independent of the parent.



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

// // Predicate to prevent fully redundant association atoms
pred noRedundantAssociationAtoms {
    all disj a1, a2: Association | not (
        a1.src = a2.src and
        a1.dst = a2.dst
        // a1.type = a2.type // Comparing types (lone sigs/atoms are comparable)
    )
}

/*
    Production 4: Association Constraints


*/
pred associationConstraints { 
    noSelfAssociation and noInterfaceToInterfaceAssociation 

    
    /*
        TODO: Add a check that asserts that two Associations do not have the same source and destination.
        This is to prevent redundant association atoms.
    */
    noRedundantAssociationAtoms

    /*
        TODO: Check to see if a Association can have its source be one class 
        and its destination be the child of that class. 
    

    */
}


// The Association relation definition 


/*
    Production 14: Reflective Association

    Given a association, the source and destination of the association must be the same class.
*/
pred reflectiveAssociation {
    // An association must be reflexive, meaning that it can be traversed in both directions.
    noRedundantAssociationAtoms    
    all r : Association | {
        // The source and destination of the association must be the same class
        (r.src = r.dst)
    }
}

// This is using Aggregation and Composition as well as Association. This is 
// a valid production.
reflectiveAssociationRun : run { 
        reflectiveAssociation and inheritanceConstraints
    } for 1 Class, 1 Association  // Run the model for 1 class and 1 association 

/*
    Production 7: Standard Association
*/
pred validAssociations {
    associationConstraints

    all r: Association | {
        // The source and destination of the association must be different classes
        (r.src != r.dst)
    }
}

/*
    NOTE: If the number of the number of classes divided by the number of association modulo 2 is not equal to 0, 
    then we need to ensure that a class does not have more than one association.
*/
runValidAssociations : run { 
        validAssociations and inheritanceConstraints
    } for 2 Class, 1 Association // Run the model for 3 classes and 2 associations


/*
    Production 8: Aggregation
*/
pred validAggregation {
    all r: Association | {
        // The source and destination of the aggregation must be different classes 
        (r.src != r.dst)
    }

}

runValidAggregation : run { validAggregation and inheritanceConstraints} for 2 Class, 1 Aggregation // Run the model for 3 classes and 2 associations

/*
    Production 9: Composition
*/
pred validComposition {
    all r: Association | {
        // The source and destination of the composition must be different classes
        (r.src != r.dst)
    }
}


/*
    We need to assert at the very least that an Aggregation relationship and 
    a Composition relationship do NOT share the same source and destination.


    Verify is it is possible or not to have two classes hold an Aggregation
    and Composition relationship when the source and destination of the two are
    flipped.
*/


pred validAssociationModel {
// associationExists and
   interfaceMultiplicity // and//
//   validAssociations and
//   noSelfAssociation and
//   noInterfaceToInterfaceAssociation and
//   noRedundantAssociationAtoms
}

// run validAssociationModel for 3 Class, 2 Interface, 10 Association
