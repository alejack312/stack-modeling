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

sig Str {
    // Define properties of the edges
    src: one Task, // Source task
    dst: one Task  // Destination task
}

// Pipe and Filter Style
sig Task {}
one sig StartTask extends Task {}  
one sig EndTask   extends Task {}  

fun follows: Task -> Task {
    Str.src -> Str.dst
}

// Pipe-and-Filter Structure (no feedback)
pred pipeFilterStructure {
  // Every stream must connect two different tasks
  all s: Str | s.src != s.dst

  // No cycles (no task eventually follows itself)
  no t: Task | t in t.^(follows)

  // Only one stream between any two tasks
  all disj s1, s2: Str | {
    s1.src = s2.src and s1.dst = s2.dst implies s1 = s2
  }

  // Every Task except the *last* in the chain must have at least one outgoing stream
  all t: Task | (some follows[t]) iff (some s: Str | s.src = t)

  // Every Task except the *first* must have at least one incoming stream
  all t: Task | (some (~follows)[t]) iff (some s: Str | s.dst = t)
}


runPipeFilterStructure : run pipeFilterStructure for 5 Str, 6 Task

/*
  Add a feedback loop: assert that there is at least one Str whose dst can 
  eventually reach its src again—i.e. a cycle exists in the follows relation.
*/
pred pipeFilterFeedback {
  // Every stream must connect two different tasks
  all s: Str | s.src != s.dst

  // There is at least one cycle in the follows relation
  some t: Task | { 
    t in t.^(follows) and t != StartTask 
  }
  // No cycles (no task eventually follows itself)
  // no t: Task | t in t.^(follows)

  // Only one stream between any two tasks
  all disj s1, s2: Str | {
    s1.src = s2.src and s1.dst = s2.dst implies s1 = s2
  }

  // Every Task except the *last* in the chain must have at least one outgoing stream
  all t: Task | (some follows[t]) iff (some s: Str | s.src = t)

  // Every Task except the *first* must have at least one incoming stream
  all t: Task | (some (~follows)[t]) iff (some s: Str | s.dst = t)
}

runPipeFilterFeedback : run pipeFilterFeedback for 7 Str, 6 Task




// ────────────────────────────────────────────────────────────
// CAPSTONE : Transformation Predicate
// ────────────────────────────────────────────────────────────

sig Before {
  streamsB: set Str,
  tasksB: set Task
}
sig After {
  streamsA: set Str,
  tasksA: set Task
}

pred transformPF[b: Before, a: After] {
  // The universe of tasks is unchanged:
  #b.tasksB = #a.tasksA and (all t: b.tasksB | t in a.tasksA)

  // Before has no feedback:
  no t: b.tasksB | t in t.^(follows)

  // There is exactly one new Str f in the After state:
  some f: Str |
    f.src = EndTask &&
    f.dst = StartTask &&
    a.streamsA = b.streamsB + f
}


// ────────────────────────────────────────────────────────────
// 4. Running the Transformation
// ────────────────────────────────────────────────────────────
// We give Forge a small universe and ask it to build
// a Before/After pair satisfying the transformPF rule.
runTransformPF: run {
  some b: Before, a: After | transformPF[b, a]
} for exactly 5 Task, exactly 6 Str, exactly 1 Before, exactly 1 After

/*
    "Graph rewriting provides a device for reusing existing products
    by performing a transformation.
    
    In general, software architecture transformation proceeds in two steps: 
    a) verify the style of an architecture; 
    b) transform an architecture from one style to another style. 
    "

    CAPSTONE : Model the transformation of a software architecture from one style to another.
*/


// “Before” snapshot: classic client–server
sig BC {         // “Before Clients”
  clientBC : set Client, // Clients in the before snapshot
  ctrlB: one Ctrl,
  dsB:   set Data
}

// “After” snapshot: distributed control–data
sig AC {         // “After Clients”
  clientAC : set Client, // Clients in the after snapshot
  ctrlA: one Ctrl,
  dsA:   set Data
}

// Source must be pure client–server: no data-server links
pred isClientServer {
  all c: BC | no c.dsB
}

// Target must allow data-server links
pred isDistributed {
  all c: AC | some c.dsA
}

pred transform {
  all b: BC, a: AC | {
    // whenever they share the same Ctrl, the DS-links satisfy the rewrite
    (b.ctrlB = a.ctrlA) implies (no b.dsB and some a.dsA)
  
    // Number of clients must be the same in both snapshots
    #b.clientBC = #a.clientAC and (all c: b.clientBC | c in a.clientAC)
  }
}

runTransform : run transform for exactly 1 BC, exactly 1 AC, exactly 5 Client, exactly 1 Ctrl, exactly 2 Data // Run the model for 5 clients and 5 servers
// Run the model for 5 clients and 5 servers
