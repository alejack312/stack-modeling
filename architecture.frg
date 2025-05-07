#lang forge


// =============================================================================
// Architectural Styles
// =============================================================================


abstract sig Server {}

one sig Ctrl extends Server {}
    // Define properties of the control server 

sig Data extends Server {}


sig Client {
    // Define properties of the client
    ctrl : one Ctrl, // Each client is associated with one control server
    ds : set Data // Each client can be associated with multiple data servers
}

pred basicClientServerStyle {  
    all c : Client | {
        some c.ctrl
        no c.ds // A client cannot be associated with a data server
    }
}

pred clientServerArchitecture {  
    // A system can only have one ControlServer
    all c : Client | {
        one c.ctrl // Each client is associated with one control server

        no c.ds // Each client cannot be associated with a data server
    }
}

runClientServerArchitecture : run clientServerArchitecture for exactly 4 Client, 1 Ctrl 

runClientServerStyle : run basicClientServerStyle for exactly 1 Client, 1 Ctrl // Run the model for 5 clients and 5 servers


pred distributedStyle {  
    // A system can only have one ControlServer
    all c : Client | {
        one c.ctrl // Each client is associated with one control server

        some c.ds // Each client can be associated with multiple data servers
    }
}

runDistributedStyle : run distributedStyle for exactly 4 Client, 1 Ctrl, 2 Data // Run the model for 5 clients and 5 servers

/*
    "Graph rewriting provides a device for reusing existing products
    by performing a transformation.
    
    In general, software architecture transformation proceeds in two steps: 
    a) verify the style of an architecture; 
    b) transform an architecture from one style to another style. 
    "

    CAPSTONE Goal: Model the transformation of a software architecture from one style to another.
*/

// Source architecture types
sig ClientS { ctrlS: one Ctrl, dsS: set Data }


// Target architecture types
sig ClientT { ctrlT: one Ctrl, dsT: set Data }
// reuse the same Ctrl, Data sigs


/*

*/

// all cS: ClientS | one cT: ClientT | ClientMap[cS] = cT

// pred transformArchitecture {
//   // 1: Same set of clients
//   #ClientS = #ClientT

//   // 2: ClientMap is a bijection
//   all cS: ClientS | one cT: ClientT | ClientMap[cS] = cT
//   all cT: ClientT | one cS: ClientS | cT = ClientMap[cS]

//   // 3: Preserve control‐server assignment
//   all cS: ClientS | {
//     let cT = ClientMap[cS] |
//       cS.ctrlS = cT.ctrlT
//   }

//   // 4: Data‐server associations only appear in the target
//   all cS: ClientS | {
//     let cT = ClientMap[cS] |
//       no cS.dsS and some cT.dsT
//   }
// }

// runTransformArchitecture : run transformArchitecture for exactly 3 Ctrl, 2 Data, 5 ClientS, 5 ClientT

sig Str {
    // Define properties of the edges
    src: one Task, // Source task
    dst: lone Task  // Destination task
}

// Pipe and Filter Style
sig Task {
    precedes: set Str, // Set of tasks that precede this task
    follows: set Str // Set of tasks that follow this task
}



// // A directed acyclic chain of Task nodes connected by Str edges.
pred pipeFilterAcyclic {  
    all t : Task | {
        // Each task must have at least one preceding and one following edge
        some t.precedes and
        some t.follows

        // No self-cycle
        (t not in t.^follows) and (t not in t.^precedes)

        // No cycles in the graph
        no (t.*follows & t.*precedes)
    }
}

runPipeFilterAcyclic : run pipeFilterAcyclic for exactly 6 Task, 11 Str // Run the model for 5 tasks and 5 edges
