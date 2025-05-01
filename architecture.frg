

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

// =============================================================================
// Root-and-Hierarchy Integrity
// =============================================================================