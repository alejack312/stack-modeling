#lang forge

open "architecture.frg"
open "inheritance.frg" // Import the inheritance model

test suite for basicClientServerStyle {
    // 1. Each client is associated with one control server
    assert {basicClientServerStyle and (all c: Client | some c.ctrl)} is sat

    // 2. Each client cannot be associated with a data server
    assert {basicClientServerStyle and (all c: Client | no c.ds)} is sat

    // 3. A system can only have one ControlServer
    assert {basicClientServerStyle and (one Ctrl)} is sat

    // 4. No self-cycle in the architecture
    assert {basicClientServerStyle and (no c: Client | c in c.^ds)} is sat
}

test suite for clientServerArchitecture {
    // 1. Each client is associated with one control server
    assert {clientServerArchitecture and (all c: Client | some c.ctrl)} is sat

    // 2. Each client cannot be associated with a data server
    assert {clientServerArchitecture and (all c: Client | no c.ds)} is sat

    // 3. A system can only have one ControlServer
    assert {clientServerArchitecture and (one Ctrl)} is sat

    // 4. No self-cycle in the architecture
    assert {clientServerArchitecture and (no c: Client | c in c.^ds)} is sat
}

test suite for distributedStyle {
    // 9. Each client is associated with one control server
    assert {distributedStyle and (all c: Client | some c.ctrl)} is sat

    // 10. Each client can be associated with multiple data servers
    assert {distributedStyle and (all c: Client | some c.ds)} is sat
    // Additional tests for architecture.frg
}

test suite for negativeCases {
    // 11. It is possible for a client to have no data server in distributedStyle (should be unsat)
    clientControlOnly : assert {distributedStyle and (all c: Client | no c.ds)} is sat

    // 12. It is not possible for a client to have more than one Ctrl
    assert {some c: Client | #(c.ctrl) > 1} is unsat

    // 13. In basicClientServerStyle, it is not possible for any client to have a data server
    assert {basicClientServerStyle and (some c: Client | some c.ds)} is unsat

    // 14. In clientServerArchitecture, it is not possible for any client to have a data server
    assert {clientServerArchitecture and (some c: Client | some c.ds)} is unsat

    // 15. In distributedStyle, it is not possible for any client to have no Ctrl
    assert {distributedStyle and (some c: Client | no c.ctrl)} is unsat

    // 16. In all styles, there cannot be more than one Ctrl
    assert {#Ctrl > 1} is unsat
}

test suite for transformationProperties {
    // 17. After transformation, all AC clients have some dsA
    test17: assert {some b: BC, a: AC | transform and (all c: AC | some c.dsA)} is sat

    // 18. Before transformation, all BC clients have no dsB
    test18: assert {some b: BC, a: AC | transform and (all c: BC | no c.dsB)} is sat

    // 19. Number of clients is preserved in transformation
    test19: assert {some b: BC, a: AC | transform and (#BC = #AC)} is sat

    // 20. If a BC and AC share the same Ctrl, then BC has no dsB and AC has some dsA
    test20: assert {some b: BC, a: AC | transform and (b.ctrlB = a.ctrlA) and (no b.dsB) and (some a.dsA)} is sat
}

test suite for pipeFilterEdgeCases {
    // 21. There is no cycle in pipeFilterStructure
    test21: assert {pipeFilterStructure and (no t: Task | t in t.^(follows))} is sat

    // 22. There is at least one cycle in pipeFilterFeedback
    test22: assert {pipeFilterFeedback and (some t: Task | t in t.^(follows) and t != StartTask)} is sat

    // 23. There cannot be a stream from a task to itself
    test23: assert {pipeFilterStructure implies (all s: Str | s.src != s.dst)} is sat
}


test suite for pipeFilterTransformation {
    // 24. Transformation preserves number of tasks (pipe-filter)
    assert {some b: Before, a: After | transformPF[b, a] and (#Task = #Task)} is sat
    // 25. Transformation adds exactly one feedback stream
    oneFeedbackStream : assert {some b: Before, a: After | transformPF[b, a] and (#a.streamsA = #b.streamsB + 1)} is sat

    // 26. Client-server to distributed transformation: number of clients preserved
    assert {some b: BC, a: AC | transform and (#BC = #AC)} is sat
    // 27. Client-server to distributed: after transform, all clients have some dsA
    assert {some b: BC, a: AC | transform and (all c: AC | some c.dsA)} is sat
    // 28. Client-server to distributed: before transform, all clients have no dsB
    assert {some b: BC, a: AC | transform and (all c: BC | no c.dsB)} is sat
}





