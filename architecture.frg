#lang forge


sig Class {
    // Define properties of the class
    inherits: set Class // Inheritance relationship
}


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
    /* How do we maintain the generalization hierarchy? */
}



run satisfiableInheritance for 5 Class // Run the model for 5 classes

// =============================================================================
// Association and Multiplicity Constraints
// =============================================================================




// =============================================================================
// Design Pattern Structure
// =============================================================================

sig Operation {}

sig Add, Remove, GetChild, Show extends Operation {}

sig Composite extends Class { 
    operations: set Operation, // Operations of the composite
    children: set Class // Children of the composite
}

sig Decorator extends Composite {
    component: one Class // The component being decorated
}

pred compositeStructure {
    some comp : Composite | {
        // A composite node must have Add, Remove, and GetChild operations
        Add in comp.operations and
        Remove in comp.operations and
        GetChild in comp.operations

        // A composite node must have at least one child
        #comp.children > 0
    }
}

// Decorator Patter

pred decoratorStructure {
    // a Decorator must wrap exactly one component and implement the Show operation.
    some dec: Decorator | {
        // A decorator must have exactly one component
        #dec.component = 1 and

        // A decorator must implement the Show operation
        Show in dec.operations and

        // A decorator must have a reference to the component it decorates
        dec.component in dec.children
    }
}

// =============================================================================
// Root-and-Hierarchy Integrity
// =============================================================================