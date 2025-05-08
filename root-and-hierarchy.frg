#lang forge 

open "inheritance.frg"
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
    topLevelClasses: set SimpleClass 
}

// A top level class that descends directly from root of graph
// is one that has no parent class, i.e.
pred hasNoParentClass[c: SimpleClass] {
    // no parent class exists s.t. c is inherited from a parent class
    no parent: SimpleClass | parent in c.inherits
}

hasNoParentClassRun: run { some c: SimpleClass | hasNoParentClass[c] } 
    for exactly 1 SimpleClass, 1 AbstractClass

// A special root node must connect to every top-level SimpleClass, i.e. every class 
// without a parent class must be in the artificial root's set of top-level 
// classes (ones with no parent class)
pred rootConnectivity {
    // if class c has no parent, then it must descend directly from the artificial
    // root of the graph
    all c: SimpleClass {
        hasNoParentClass[c] implies (
            c in Root.topLevelClasses
        )
    }
    // if class c descends directly from the artificial root of the graph, then it
    // must have no parent class
    all c: SimpleClass {
        c in Root.topLevelClasses implies (
            hasNoParentClass[c]
        )
    }
}

rootConnectivityRun: run rootConnectivity for exactly 5 SimpleClass, exactly 5 AbstractClass

// Graph must maintain root-and-hierarchy integrity for it to be well-formed
// and able to undergo verification, i.e. this predicate lists the predicates that
// must hold true before the graph can be verified
pred rootAndHierarchyIntegrity {
    inheritanceConstraints and // no class inherits from both a parent and grandparent simultaneously
    (singleInheritance or multipleInheritance) and // single or multiple inheritance
    rootConnectivity // all classes with no parent class descend directly from root node
}

rootAndHierarchyIntegrityRun: run rootAndHierarchyIntegrity for exactly 5 SimpleClass, exactly 5 AbstractClass, exactly 0 Interface