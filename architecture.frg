#lang forge


abstract sig Classifier {} // Abstract parent for Class and Interface

sig Class {
    // Define properties of the class
    inherits: set Class // Inheritance relationship
}

sig Interface extends Classifier {} // Define Interface signature


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



pred satisfiableInheritance {
    classExists and noSelfInheritance and linearInheritance and noRedundantInheritance and (
        singleInheritance or multipleInheritance) // At least one class exists and no self-inheritance and inheritance is not symmetric
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
}

//run satisfiableInheritance for 5 Class 

// =============================================================================
// Association and Multiplicity Constraints
// =============================================================================

// The types of associations allowed between Classes
abstract sig AssociationType {}
one sig Association, Aggregation, Composition extends AssociationType {} 

// The Association relation definition 
sig Associate {
    src: one Classifier,    // Source of the association
    dst: one Classifier,    // Destination of the association
    type: lone AssociationType // Type of the association
}

// Interface Attachment
pred interfaceMultiplicity {
    all i: Interface | one c: Class | {
        // Assumes attachment is represented by an Associate where Interface is src and Class is dst
        some a: Associate | (a.src = i and a.dst = c) or (a.src = c and a.dst = i) 
    }
}

// Valid Association Types
pred validAssociations {
    all a: Associate | {
        // If an association has one of the specified types
        a.type in Association + Aggregation + Composition implies {
            //then both its source and destination must be Classes.
            a.src in Class and a.dst in Class
        }
        // If src or dst is an Interface, type must be empty?
        (a.src in Interface or a.dst in Interface) implies no a.type
    }
}

// Predicate to prevent self-associations
pred noSelfAssociation {
    no a: Associate | a.src = a.dst
}

// Predicate to prevent direct Interface-to-Interface associations
pred noInterfaceToInterfaceAssociation {
    no a: Associate | a.src in Interface and a.dst in Interface
}

// Predicate to prevent fully redundant association atoms
pred noRedundantAssociationAtoms {
    all disj a1, a2: Associate | not (
        a1.src = a2.src and
        a1.dst = a2.dst and
        a1.type = a2.type // Comparing types (lone sigs/atoms are comparable)
    )
}


pred validAssociationModel {
   interfaceMultiplicity // and//
//   validAssociations and
//   noSelfAssociation and
//   noInterfaceToInterfaceAssociation and
//   noRedundantAssociationAtoms
}

run validAssociationModel for 3 Class, 2 Interface, 10 Associate



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

//run compositeStructure for 5 Class // Run the model for 5 classes

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


// // A directed acyclic chain of Task nodes connected by Str edges.
// pred pipeFilterAcyclic[] {  
//   no t: Task | t in t.*follows  
// }=============================================================================
// Root-and-Hierarchy Integrity
// =============================================================================