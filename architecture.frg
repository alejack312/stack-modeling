#lang forge


abstract sig Classifier {} // Abstract parent for Class and Interface

sig Class {
    // Define properties of the class
    inherits: set Class // Inheritance relationship
}

sig Interface extends Classifier {
    implementer : one Class
} // Define Interface signature


// =============================================================================
// Inheritance relationship
// =============================================================================

pred classExists {
    some c: Class | #c.inherits > 0 // At least one class exists
}


// No class should inherit from itself
pred noSelfInheritance {
    no c : Class | c in c.inherits // No class should inherit from itself 
}

pred linearInheritance {
    // A class should not inherit from its own subclass at any level
    all c: Class | {
        not (c in c.^inherits) // No class should inherit from its own subclass at any level
    }
}

/*
    NOTE! The following predicate is a solution to the problem of redundant inheritance.
    Discuss how we came across this in the design process and how we solved it.
*/
pred noRedundantInheritance {
    // A class should not inherit from its "parent" and its "grandparent" at the same time
    
    all c: Class | {
        no p, a: Class |
        p in c.inherits &&
        a in p.^inherits &&     -- a is a true ancestor of p (one-or-more hops)
        a in c.inherits
    }
}

pred inheritanceConstraints {
    noSelfInheritance and linearInheritance and noRedundantInheritance
}

// Production 10 which permits exactly one "p"-edge per subclass
pred singleInheritance {
    some c: Class | {
        lone p : Class | p in c.inherits // Each class can have at most one parent
    }
}


/* 
    Production 13

    Removing production 13 disallows multiple inheritance.
*/
pred multipleInheritance {
    some c: Class | {
        #c.inherits > 1 // Each class can have multiple parents
    }
}





/*
    In UML, the generalization specifics a hierarchical relationship between a
    general description and a specific description. 

    In the node-edge representation, a line, which links from the vertex labeled 
    c in a Class node to the vertex labeled p in the other Class node, designates
    the generalization relationship from the former class to the latter. In other
    words, the vertex labeled c indicates the general class, and the vertex labeled
    p denotes the specific class accordingly.

    Generalization hierarchy should be maintained. Classes should always be 
    linked from most general to most specific. 
*/

pred generalization { 
    /* 
        How do we maintain the generalization hierarchy? 
    
        Productions 10 and 13, single inheritance and multiple inheritance, 
        demonstrate the generalization.
    */
    
    // At least one class exists and no self-inheritance and inheritance is not symmetric
    classExists and noSelfInheritance and linearInheritance and noRedundantInheritance and (
        singleInheritance or multipleInheritance) 
}




// =============================================================================
// Interfaces
// =============================================================================


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

run generalization for 5 Class // Run the model for 5 classes


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
    
    all r : Association | {
        // The source and destination of the association must be the same class
        (r.src = r.dst)
    }
}

// This is using Aggregation and Composition as well as Association. This is 
// a valid production.
reflectiveAssociationRun : run { reflectiveAssociation and inheritanceConstraints} for 1 Class, 1 Association  // Run the model for 1 class and 1 association 

/*
    Production 7: Standard Association
*/
pred validAssociations {
    all r: Association | {
        // The source and destination of the association must be different classes
        (r.src != r.dst)
    }
}

/*
    NOTE: If the number of the number of classes divided by the number of association modulo 2 is not equal to 0, 
    then we need to ensure that a class does not have more than one association.
*/
runValidAssociations : run { validAssociations and inheritanceConstraints} for 2 Class, 1 Association // Run the model for 3 classes and 2 associations


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



// =============================================================================
// Design Pattern Structure
// =============================================================================

abstract sig Operation {}
one sig Add, Remove, GetChild extends Operation {}

abstract sig Component {
    children: set Component   // composite holds references to sub-components
}

sig Leaf extends Component {}

sig Composite extends Component {
    compOps: set Operation          // operations implemented by composite
}

sig Decorator extends Component {
  wraps: one Component,      // the component being decorated
  decOps: set Operation         // supported operations (e.g., Show)
}

one sig Show extends Operation {}

pred compositeStructure {
    some comp : Composite | {
        // A composite node must have Add, Remove, and GetChild operations
        Add in comp.compOps and
        Remove in comp.compOps and
        GetChild in comp.compOps

        // A composite node must have at least one child
        #comp.children > 0
    }
}

// run compositeStructure for 5 Class // Run the model for 5 classes


// Decorator Patter

pred decoratorStructure {
    // a Decorator must wrap exactly one component and implement the Show operation.
    some dec: Decorator | {
        // A decorator must have exactly one component
        #dec.wraps = 1 and

        // A decorator must implement the Show operation
        Show in dec.decOps and

        // A decorator must have a reference to the component it decorates
        dec.wraps in dec.children
    }
}

//run decoratorStructure for 1 Class // Run the model for 5 classes

// =============================================================================
// Architectural Styles
// =============================================================================

sig Client {
    // Define properties of the client
    connects: set Server // Set of servers connected to this client
}

sig Server {
    // Define properties of the server
    connected: set Client // Set of clients connected to this server
}

pred clientServerStyle {  
    one s: Server |  { 
        all c: Client | c in s.connected
    }
}


sig ControlServer, DataServer extends Server {}

pred distributedStyle {  
    one ctrl: ControlServer | some ds: DataServer | {
        all c: Client | {
            (c in ctrl.connected) and 

        (some d: DataServer | connects[ctrl][d]  )

        }
    }  
}

sig Task {
    follows: set Task // Set of tasks that follow this task
}




// // A directed acyclic chain of Task nodes connected by Str edges.
pred pipeFilterAcyclic {  
  no t: Task | t in t.*follows  
}


// =============================================================================
// Root-and-Hierarchy Integrity
// =============================================================================

// Production 15 (Initial State):
// 1. Exactly 1 Root exists
// 2. All top-level classes (classes with no parent class) descend from Root

// Define properties of the special "root" of the graph, which is not a class 
// in and of itself and is artificially introduced to facilitate verification
// of graph structure
one sig Root {
    // set of top-level classes with no parent class
    // that descend directly from artificial root of graph
    topLevelClasses: set Class 
}

// A top level class that descends directly from root of graph
// is one that has no parent class, i.e.
pred hasNoParentClass[c: Class] {
    // no parent class exists s.t. c is inherited from a parent class
    no parent: Class | parent in c.inherits
}

// A special root node must connect to every top-level Class, i.e. every class 
// without a parent class must be in the artificial root's set of top-level 
// classes (ones with no parent class)
pred rootConnectivity {
    // if class c has no parent, then it must descend directly from the artificial
    // root of the graph
    all c: Class {
        hasNoParentClass[c] implies (
            c in Root.topLevelClasses
        )
    }
    // if class c descends directly from the artificial root of the graph, then it
    // must have no parent class
    all c: Class {
        c in Root.topLevelClasses implies (
            hasNoParentClass[c]
        )
    }
}

// Graph must maintain root-and-hierarchy integrity for it to be well-formed
// and able to undergo verification, i.e. this predicate lists the predicates that
// must hold true before the graph can be verified
pred rootAndHierarchyIntegrity {
    noSelfInheritance // no class inherits from itself
    linearInheritance // a class should not inherit from its own subclass at any level
    singleInheritance // every class has at most one parent
    noRedundantInheritance // no class inherits from both a parent and grandparent simultaneously
    rootConnectivity // all classes with no parent class descend directly from root node
}

rootAndHierarchyIntegrityRun: run rootAndHierarchyIntegrity for exactly 5 Class