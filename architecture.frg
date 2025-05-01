

sig Class {
    // Define properties of the class
    inherits: set Class // Inheritance relationship
}


// =============================================================================
// Inheritance relationship
// =============================================================================

pred singleInheritance {
    all c: Class | {
        lone p : Class | {} // inherits[c][p]
    }
}


// No class should inherit from itself
pred noSelfInheritance {
    no c : Class | c in c.*inherits
}

// Generalization hierarchy should be maintained. Classes should always be
// linked from most general to most specific. 

pred generalization { 
    /* How do we maintain the generalization hierarchy? */
}


// =============================================================================
// Association and Multiplicity Constraints
// =============================================================================




// =============================================================================
// Design Pattern Structure
// =============================================================================

sig Operation {}

sig Add, Remove, GetChild extends Operation {}

sig Composite extends Class { 
    operations: set Operation // Operations of the composite
    children: set Class // Children of the composite
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