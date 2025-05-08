#lang forge

open "design-pattern.frg" // Import the design pattern model
open "inheritance.frg" // Import the inheritance model

test suite for compositeStructure {
    // Checks that every Composite has at least one child
    assert {
        compositeStructure and (all comp: Composite | { 
                some comp.childrenC
        })
    } is sat
    // Checks that every Composite has Add, Remove, and GetChild in its compOps
    assert {
        compositeStructure and (all comp: Composite | Add in comp.compOps and Remove in comp.compOps and GetChild in comp.compOps)} is sat
    
    // Checks that for every Composite, there is some Class that implements its interface
    assert {
        compositeStructure and (all comp: Composite | {
            some c: AbstractClass | #c.implements = 1 and c.implements = comp.implementsC
        })
    } is sat
    
    // Checks that no Composite is in its own transitive children (no cycles)
    assert {
        compositeStructure and (no comp: Composite | comp in comp.^childrenC)
    } is sat
    
    // Checks that no Decorator wraps a class that is in the transitive children of any Composite
    // (TODO: Check if this is correct)
    assert {
        compositeStructure and (no d: Decorator | {
            all comp: Composite | d.wraps in comp.^childrenC
        })
    } is sat
    
    // Checks that all Composites have different implementsC
    assert {
        compositeStructure and (all disj c1, c2: Composite | c1.implementsC != c2.implementsC)
    } is sat
    
    // Duplicate: Checks that no Composite is in its own transitive children (no cycles)
    assert {
        compositeStructure and (no comp: Composite | comp in comp.^childrenC)
    } is sat
    
    // Checks that the children sets of any two distinct Composites are disjoint
    assert {
        compositeStructure and (all disj c1, c2: Composite | { 
            no (c1.childrenC & c2.childrenC)
        })
    } is sat
    
    
    
    // Checks that only Composites have Add, Remove, GetChild in compOps
    assert {
        compositeStructure and (all c: Component - Composite | Add not in c.(compOps) and Remove not in c.(compOps) and GetChild not in c.(compOps))
    } is sat


    // Checks that all children of a Composite are either a Leaf or a Composite
    assert {
        compositeStructure and (all comp: Composite | {
            all child: comp.childrenC | child in Leaf + Composite
        })
    } is sat

    // Checks that if a Composite has a Composite child, they must have the same implementsC
    assert {compositeStructure and (all comp: Composite | {
        all child: comp.childrenC | child in Composite implies child.implementsC = comp.implementsC
        })
    } is sat
    
    // Checks that no Decorator is in the transitive children of any Composite
    assert {compositeStructure and (all comp: Composite | {all d: Decorator | d not in comp.^childrenC})} is sat
    
    // Checks that no Composite is its own direct child
    assert {compositeStructure and (all comp: Composite | comp not in comp.childrenC)} is sat
    
    // Checks that no Composite has itself as a child (redundant with above)
    assert {compositeStructure and (all comp: Composite | {all child: comp.childrenC | child != comp})} is sat
}

test suite for decoratorStructure {
    
    // Checks that every Decorator wraps exactly one class
    assert {decoratorStructure and (all dec: Decorator | #dec.wraps = 1)} is sat
    
    // Checks that every Decorator has Show in its decOps
    assert {decoratorStructure and (all dec: Decorator | Show in dec.decOps)} is sat
    
    // Checks that no Decorator wraps itself
    assert {decoratorStructure and (all dec: Decorator | dec.wraps != dec)} is sat
    
    // Checks that no Decorator is in its own transitive wraps (no cycles)
    assert {decoratorStructure and (no dec: Decorator | dec in dec.^wraps)} is sat
    
    // Test that checks if a decorator is not in the children of its wrapped component
    // (TODO: Check if this is correct)
    assert {decoratorStructure and (no d: Decorator | {
            all comp: Composite | d.wraps in comp.^childrenC
    })} is sat
    
    // Checks that all Decorators wrap different classes
    assert {decoratorStructure and (all disj d1, d2: Decorator | d1.wraps != d2.wraps)} is sat
    
    // Checks that no Decorator is in its own transitive wraps (duplicate)
    assert {decoratorStructure and (all dec: Decorator | dec not in dec.^wraps)} is sat
    
    // Checks that only Decorators have Show in decOps
    assert {decoratorStructure and (all c: Component - Decorator | Show not in c.(decOps))} is sat
    
    // Checks that every Decorator's implementsD matches the implements of what it wraps
    assert {decoratorStructure and (all dec: Decorator | dec.implementsD = dec.wraps.implements)} is sat
    
    // Checks that every Decorator wraps a Class
    assert {decoratorStructure and (all dec: Decorator | dec.wraps in AbstractClass)} is sat
    
    // Checks that Decorators do not wrap Composites or Leafs
    assert {decoratorStructure and (all dec: Decorator | dec.wraps not in Composite + Leaf)} is sat
    
    // Checks that the implements of the wrapped class matches the Decorator's implementsD
    assert {decoratorStructure and (all dec: Decorator | dec.wraps.implements = dec.implementsD)} is sat
    
    // Checks that no Decorator is a child of any Composite
    assert {decoratorStructure and (all dec: Decorator | {all comp: Composite | dec not in comp.childrenC})} is sat
}

// =====================
// Example tests for Composite pattern
// =====================
example compositeValid is {compositeStructure} for {
    Composite = `Comp0
    Leaf = `Leaf0
    Component = `Comp0 + `Leaf0
    AbstractClass = `Class0
    SimpleClass = `Class0
    Interface = `Iface0
    Add = `Add0
    Remove = `Remove0
    GetChild = `GetChild0
    Show = `Show0
    Operation = `Add0 + `Remove0 + `GetChild0 + `Show0
    `Comp0.implementsC = `Iface0
    `Comp0.childrenC = `Leaf0
    `Comp0.compOps = `Add0 + `Remove0 + `GetChild0
    `Class0.implements = `Iface0
}

example compositeInvalidSelfChild is {not compositeStructure} for {
    Composite = `Comp0
    Leaf = `Leaf0
    Component = `Comp0 + `Leaf0
    AbstractClass = `Class0
    SimpleClass = `Class0
    Interface = `Iface0
    Add = `Add0
    Remove = `Remove0
    GetChild = `GetChild0
    Show = `Show0
    Operation = `Add0 + `Remove0 + `GetChild0 + `Show0
    `Comp0.implementsC = `Iface0
    `Comp0.childrenC = `Comp0
    `Comp0.compOps = `Add0 + `Remove0 + `GetChild0
    `Class0.implements = `Iface0
}

// =====================
// Example tests for Decorator pattern
// =====================
example decoratorValid is {decoratorStructure} for {
    Decorator = `Dec0
    Component = `Dec0
    AbstractClass = `Class0
    SimpleClass = `Class0
    Interface = `Iface0
    Show = `Show0
    Add = `Add0
    Remove = `Remove0
    GetChild = `GetChild0
    Operation = `Add0 + `Remove0 + `GetChild0 + `Show0
    `Dec0.implementsD = `Iface0
    `Dec0.wraps = `Class0
    `Dec0.decOps = `Show0
    `Class0.implements = `Iface0
}

example decoratorInvalidSelfWrap is {not decoratorStructure} for {
    Decorator = `Dec0
    Component = `Dec0
    AbstractClass = `Dec0 + `Class0
    SimpleClass = `Dec0 + `Class0
    Interface = `Iface0
    Show = `Show0
    Add = `Add0
    Remove = `Remove0
    GetChild = `GetChild0
    Operation = `Add0 + `Remove0 + `GetChild0 + `Show0
    `Dec0.implementsD = `Iface0
    `Dec0.wraps = `Dec0
    `Dec0.decOps = `Show0
    `Class0.implements = `Iface0
}