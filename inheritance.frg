#lang forge


// =============================================================================
// Interfaces
// =============================================================================


/*
    NOTE: Design choice to remove the implementer field from the Interface sig
    Instead, we are giving the SimpleClass sig a set of interfaces it implements.

    We did this in order to allow for multiple inheritance of interfaces, specifically,
    to model the Capstone exploration of the Java programming language. 

*/

sig Field {}
sig Method {}

sig Interface {
    methodsI: set Method, // Methods defined in the interface
    fieldsI: set Field // Fields defined in the interface
} // Define Interface signature

abstract sig AbstractClass {
    inherits: set AbstractClass, // Inheritance relationship
    implements: set Interface // Interfaces implemented by the class
} // defines abstract class signature

sig SimpleClass extends AbstractClass{}

// =============================================================================
// Inheritance relationship
// =============================================================================

pred classExists {
    some c: AbstractClass | #c.inherits > 0 // At least one class exists
}


// No class should inherit from itself
pred noSelfInheritance {
    no c : AbstractClass | c in c.inherits // No class should inherit from itself 
}

pred linearInheritance {
    // A class should not inherit from its own subclass at any level
    all c: AbstractClass | {
        not (c in c.^inherits) // No class should inherit from its own subclass at any level
    }
}

/*
    NOTE! The following predicate is a solution to the problem of redundant inheritance.
    Discuss how we came across this in the design process and how we solved it.
*/
pred noRedundantInheritance {
    // A class should not inherit from its "parent" and its "grandparent" at the same time
    
    all c: AbstractClass | {
        no p, a: AbstractClass |
        p in c.inherits &&
        a in p.^inherits &&     -- a is a true ancestor of p (one-or-more hops)
        a in c.inherits
    }
}

pred inheritanceConstraints {
    noSelfInheritance and linearInheritance and noRedundantInheritance

    // No class should inherit from a class that implements the same interface
    // all disj c1, c2: AbstractClass | {
    //     c1 in c2.inherits implies {
    //         (some i : Interface | i in c1.implements and not (i in c2.implements))
    //     }
    // }
    all disj c1, c2: AbstractClass | {
        (some Interface) implies (
            (c1 in c2.inherits) implies (
                some i: Interface | i in c1.implements and not (i in c2.implements)
            )
        )
    }
}

// Production 10 which permits exactly one "p"-edge per subclass
pred singleInheritance {
    some c: AbstractClass | {
        lone p : AbstractClass | p in c.inherits // Each class can have at most one parent
    }
}


/* 
    Production 13

    Removing production 13 disallows multiple inheritance.
*/
pred multipleInheritance {
    some c: AbstractClass | {
        #c.inherits > 1 // Each class can have multiple parents
    }
}

/*
    In UML, the generalization specifics a hierarchical relationship between a
    general description and a specific description. 

    In the node-edge representation, a line, which links from the vertex labeled 
    c in a AbstractClass node to the vertex labeled p in the other AbstractClass node, designates
    the generalization relationship from the former class to the latter. In other
    words, the vertex labeled c indicates the general class, and the vertex labeled
    p denotes the specific class accordingly.

    Generalization hierarchy should be maintained. AbstractClasses should always be 
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

runGeneralization : run generalization for exactly 5 SimpleClass, exactly 5 AbstractClass // Run the model for 5 classes

/*
    Production 6: One Interface per AbstractClass

    To TEST:
    A graph specifying structure is invalid if it breaks at least one relationship
    specified in any production. For example, Production 6 in Figure 3 define one 
    interface can only attach to one class. If an interface is designed to be 
    related to more than one class, a parser can indicate a violation of 
    Production 6. 

*/
pred interfaceMultiplicity {
    all c : AbstractClass | {
        #c.implements = 1 or #c.implements = 0 // A class can implement at most one interface
    }  
}


/*
    NOTE: Found a case where a class was inheriting from a class that implements
    the same interface.
*/
runInterfaceMultiplicity : run { 
    interfaceMultiplicity and inheritanceConstraints 
} for exactly 2 AbstractClass, exactly 2 SimpleClass, 1 Interface // Run the model for 2 classes and 1 interface

// ============================================================================
// CAPSTONE : Resolutions for Multiple Inheritance
// ============================================================================

/*
    What happens in the presence of multiple inheritance? It would be cool to 
    show there can be multiple resolution policies that apply if there is a 
    clash between two parents.
*/

sig ExtendedClass extends AbstractClass{
    // Define properties of an extended class
    parentOrder: pfunc ExtendedClass -> Int,   // an index for each parent
    methodsC: set Method, // Methods defined in the class
    fieldsC: set Field, // Fields defined in the class
    policy: one ResolutionPolicy // Resolution policy for multiple inheritance
}

abstract sig ResolutionPolicy {}
one sig LeftWins, RightWins, RequireOverride, MergeAll extends ResolutionPolicy {}

pred interfacesOnly {
    // Java does not allow multiple inheritance of classes, but it does allow
    // multiple inheritance of interfaces.

    not multipleInheritance // No multiple inheritance of classes

    (all c : AbstractClass | {
        c.inherits = c.inherits - c.implements // ExtendedClasses cannot inherit from interfaces

        c.implements = c.implements - c.inherits // Interfaces cannot inherit from classes

        // Check that a class cannot implement the same interface more than once

        #c.implements > 1 // A class can implement multiple interfaces
    }) 

    // No class implements an interface that is implemented by any of its ancestors
    all c: AbstractClass | no (c.implements & (c.^inherits).implements)
}

/*
    NOTE: Ran into the issue where a class is inheriting from a class that implements
    the same interface. 

    Fix by
*/


runInterfacesOnly : run {
    interfacesOnly and inheritanceConstraints 
} for exactly 5 SimpleClass, exactly 5 AbstractClass, 5 Interface // Run the model for 5 classes and 2 interfaces


pred resolution {
    all c: ExtendedClass |
        // If LeftWins: choose the first parent that does not inherit from any other parent
        (c.policy = LeftWins) implies (
            (some p: c.inherits | 
                all q: c.inherits | parentOrder[c][p] <= parentOrder[c][q] =>
                p.methodsC in c.methodsC and p.fieldsC in c.fieldsC)
        )
      // If RightWins: choose the last parent that does not inherit from any other parent
    &&  (c.policy = RightWins) implies (
        (some p: c.inherits |
                all q: c.inherits | parentOrder[c][p] >= parentOrder[c][q] =>
                p.methodsC in c.methodsC and p.fieldsC in c.fieldsC)
        )
      // If RequireOverride: subclass must declare its own methods for any inherited conflict
      
    &&  (c.policy = RequireOverride) implies (
            all p1, p2: c.inherits |
              p1 != p2 implies (
                // Design Check: What do we want to include in the class methods?
                // If Parent1 and Parent2 both have foo, and Child inherits from both with RequireOverride, 
                // then foo must be in Child.methodsC.
                let notShared = p1.methodsC - p2.methodsC |
                   all m: notShared | m in c.methodsC
              )
        )
      // If MergeAll: subclass automatically includes all methods of all parents
    &&  (c.policy = MergeAll) implies (
            all p: c.inherits | (p.methodsC in c.methodsC) and (p.fieldsC in c.fieldsC)
        )
}

runResolution : run {
    resolution and inheritanceConstraints 
} for exactly 5 ExtendedClass, exactly 5 AbstractClass, 5 Interface

