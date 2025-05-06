// #lang forge

// open architecture.frg

// test suite for compositeStructure {

//     assert all c : Composite | {
//         (Add in c.compOps) and
//         (Remove in c.compOps) and
//         (GetChild in c.compOps)
//     }

//     assert l : Leaf | no l.children
// }

// test suite for decoratorStructure { 

//     assert all d : Decorator | d.wraps != d

//     assert all d : Decorator | Show in d.decOps
// }