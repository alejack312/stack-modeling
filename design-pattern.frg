#lang forge

open "inheritance.frg"

// =============================================================================
// Design Pattern Structure
// =============================================================================

abstract sig Component {}


sig Leaf extends Component {}


abstract sig Operation {}
one sig Add, Remove, GetChild, Show  extends Operation {}

// Maybe add leaf sig



sig Composite extends Component {
    implementsC: one Interface, // interfaces implemented by the composite
    childrenC: set Component,   // composite holds references to sub-components
    compOps: set Operation          // operations implemented by composite
}

/*
    The Decorator pattern allows behavior to be added to individual objects, 
    without modifying the original class or affecting other objects from the 
    same class.
*/
sig Decorator extends Component {
  implementsD: one Interface, // interfaces implemented by the decorator
  wraps: one AbstractClass,      // the component being decorated
  decOps: set Operation      // supported operations (e.g., Show)
}

pred compositeStructure {
    all comp : Composite | {
        some c : AbstractClass | {
            #c.implements = 1
            c.implements = comp.implementsC 
        }

        // A composite node must have Add, Remove, and GetChild operations
        Add in comp.compOps and
        Remove in comp.compOps and
        GetChild in comp.compOps


        some comp.implementsC 
        // A composite node must have at least one child
        some comp.childrenC and (comp not in comp.^childrenC)
        // No self-cycle
        // comp not in comp.^children

        // No Decorator may be in its wrapper’s children
        //all d: Decorator | d not in (d.wraps.(comp.^children))
    }

}


runCompositeStructure : run {
    compositeStructure and inheritanceConstraints 
} for exactly 1 Composite, exactly 1 SimpleClass, exactly 1 AbstractClass, exactly 2 Component, exactly 1 Interface, exactly 0 Decorator

// Decorator Patter

pred decoratorStructure {
    // a Decorator must wrap exactly one component and implement the Show operation.
    all dec: Decorator | {
        // A decorator must have exactly one component

        // This class is the base object
        some c : AbstractClass | {
            #c.implements = 1
            c.implements = dec.implementsD 
        }

        // A decorator must implement the Show operation
        Show in dec.decOps and

        // A decorator must have a reference to the component it decorates
        //dec.wraps != dec

        -- Decorator cannot be its own descendant via children
        dec not in dec.^wraps 
        -- Decorator cannot wrap a component that contains it
        // dec not in (dec.wraps.^(Composite.children))
    }
}



runDecoratorStructure : run {
    decoratorStructure and inheritanceConstraints 
} for exactly 1 Decorator, exactly 1 SimpleClass, exactly 1 AbstractClass, exactly 1 Interface, exactly 0 Composite
    
