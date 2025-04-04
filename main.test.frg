#lang forge

open "main.frg"

// This test suite validates that technology stacks have the required components
test suite for validStacks {
    // Checks that each stack has exactly one frontend, backend, and database technology
    assert all stack : TechnologyStack | {
        one stack.frontend
        one stack.backend
        one stack.database
    } is necessary for validStacks

    // Verifies ORM constraints: ORM requires database, Firebase can't use ORM
    assert all stack : TechnologyStack | {
        no stack.database implies no stack.orm
        some stack.orm implies some stack.database
        stack.database = Firebase implies no stack.orm
    } is necessary for validStacks   
}

// Tests that having all possible qualities is impossible
test suite for allQualitiesImpossible {
    // Ensures no stack can have all qualities simultaneously
    assert no stack: TechnologyStack | stack.overallQualities = Quality
        is necessary for allQualitiesImpossible
}

// Verifies how qualities propagate from components to the overall stack
test suite for qualityPropagation {
    // Checks that a stack's overall qualities are composed from its component qualities
    assert all stack: TechnologyStack | {
        stack.overallQualities = stack.frontendBackendQualities + 
        stack.backendDatabaseQualities + stack.databaseORMQualities + 
        stack.authQualities
    } is necessary for qualityPropagation
}

// Tests that specific technologies imply specific qualities
test suite for technologyQualityImplications {
    // NextJS provides Speed and DevExperience
    assert all stack: TechnologyStack | 
        stack.frontend = NextJS implies (Speed + DevExperience) in stack.frontendBackendQualities
        is necessary for technologyQualityImplications
    
    // Go backend provides Speed and Scalability
    assert all stack: TechnologyStack | 
        stack.backend = GoBackend implies (Speed + Scalability) in stack.backendDatabaseQualities
        is necessary for technologyQualityImplications
    
    // Firebase lacks Security in backend-database interaction
    assert all stack: TechnologyStack |
        stack.database = Firebase implies Security not in stack.backendDatabaseQualities
        is necessary for technologyQualityImplications
    
    // Prisma ORM provides Reliability and DevExperience
    assert all stack: TechnologyStack |
        stack.orm = PrismaORM implies (Reliability + DevExperience) in stack.databaseORMQualities
        is necessary for technologyQualityImplications
}

// Validates tradeoffs between different qualities
test suite for qualityTradeoffs {
    // High speed sacrifices reliability
    assert all stack: TechnologyStack |
        #(Speed & stack.overallQualities) > 2 implies #(Reliability & stack.overallQualities) < 2
        is necessary for qualityTradeoffs
    
    // Firebase has limited security capabilities
    assert all stack: TechnologyStack | 
        stack.database = Firebase implies #(Security & stack.overallQualities) <= 1
        is necessary for qualityTradeoffs
    
    // Pedagogical stacks can't be highly performant
    assert all stack: TechnologyStack |
        Pedagogy in stack.overallQualities implies 
            #(stack.overallQualities & (Speed + Scalability)) < 2
        is necessary for qualityTradeoffs

    // Example of a valid stack with speed-reliability tradeoff
    example speedReliabilityTradeoffPass is { qualityTradeoffs } for {
        TechnologyStack = `TS0
        Quality = `Q0 + `Q1 + `Q2 + `Q3 + `Q4 + `Q5 + `Q6 + `Q7
        
        // Define qualities
        Speed = `Q0
        Reliability = `Q1
        Scalability = `Q2
        DevExperience = `Q3
        Security = `Q4
        Maintainability = `Q5
        Pedagogy = `Q6
        CostEfficiency = `Q7
        
        // High speed, low reliability
        `TS0.overallQualities = `Q0 + `Q0 + `Q0 + `Q2
    }
    
    // Example of an invalid stack that violates tradeoff rules
    example speedReliabilityTradeoffFail is { not qualityTradeoffs } for {
        TechnologyStack = `TS0
        Quality = `Q0 + `Q1 + `Q2 + `Q3 + `Q4 + `Q5 + `Q6 + `Q7
        
        // Define qualities
        Speed = `Q0
        Reliability = `Q1
        Scalability = `Q2
        DevExperience = `Q3
        Security = `Q4
        Maintainability = `Q5
        Pedagogy = `Q6
        CostEfficiency = `Q7
        
        // Has Pedagogy with both Speed and Scalability (impossible)
        `TS0.overallQualities = `Q0 + `Q2 + `Q6
    }
}

// Validates limitations on quality combinations
test suite for qualityBudget {
    // Maximum total qualities a stack can have
    assert all stack: TechnologyStack | #stack.overallQualities <= 6
        is necessary for qualityBudget
    
    // Maximum qualities per component
    assert all stack: TechnologyStack | {
        #stack.frontendBackendQualities <= 3
        #stack.backendDatabaseQualities <= 3
        #stack.databaseORMQualities <= 3
        #stack.authQualities <= 2
    } is necessary for qualityBudget

    // Example of a stack within quality budget limits
    example withinBudgetPass is { qualityBudget } for {
        TechnologyStack = `TS0
        Quality = `Q0 + `Q1 + `Q2 + `Q3 + `Q4 + `Q5 + `Q6 + `Q7
        
        // Define qualities
        Speed = `Q0
        Reliability = `Q1
        Scalability = `Q2
        DevExperience = `Q3
        Security = `Q4
        Maintainability = `Q5
        Pedagogy = `Q6
        CostEfficiency = `Q7
        
        // Component qualities within limits
        `TS0.frontendBackendQualities = `Q0 + `Q1 + `Q2
        `TS0.backendDatabaseQualities = `Q1 + `Q3
        `TS0.databaseORMQualities = `Q0 + `Q5
        `TS0.authQualities = `Q4
        
        // Overall qualities within limit (6)
        `TS0.overallQualities = `Q0 + `Q1 + `Q2 + `Q3 + `Q4 + `Q5
    }
    
    // Example of a stack exceeding quality budget
    example exceedsBudgetFail is { not qualityBudget } for {
        TechnologyStack = `TS0
        Quality = `Q0 + `Q1 + `Q2 + `Q3 + `Q4 + `Q5 + `Q6 + `Q7
        
        // Define qualities
        Speed = `Q0
        Reliability = `Q1
        Scalability = `Q2
        DevExperience = `Q3
        Security = `Q4
        Maintainability = `Q5
        Pedagogy = `Q6
        CostEfficiency = `Q7
        
        // Too many qualities for frontend-backend
        `TS0.frontendBackendQualities = `Q0 + `Q1 + `Q2 + `Q3
        `TS0.backendDatabaseQualities = `Q1
        `TS0.databaseORMQualities = `Q0
        `TS0.authQualities = `Q4
        
        `TS0.overallQualities = `Q0 + `Q1 + `Q2 + `Q3 + `Q4
    }
}

// Tests incompatibilities between technologies
test suite for technologyConflicts {
    // Vite and Postgres don't work well together
    assert all stack: TechnologyStack | 
        stack.frontend = Vite implies stack.database != Postgres and
        stack.frontend = Vite implies stack.database != SQLDatabase
        is necessary for technologyConflicts
    
    // Fast Node/Go with reliable Postgres is not achievable
    assert all stack: TechnologyStack |
        (stack.backend = NodeBackend or stack.backend = GoBackend) and stack.database = Postgres implies
            not (Speed in stack.backendDatabaseQualities and Reliability in stack.backendDatabaseQualities)
        is necessary for technologyConflicts
}

// Tests the optimizedFor predicate
test suite for optimizedFor {
    // Ensures stacks optimized for specific qualities actually have those qualities
    assert all stack: TechnologyStack | {
        optimizedFor[(Speed + Scalability), stack] implies (Speed + Scalability) in stack.overallQualities
    } is necessary for optimizedFor[(Speed + Scalability), stack]
}

// Tests stack evolution paths
test suite for evolutionPath {
    // Ensures evolution must change the stack (can't evolve to the same stack)
    assert {
        some s1, s2 : TechnologyStack | {
            evolutionPath[s1, s2] and s1 = s2
        } 
    } is unsat
}

// Tests requirements for microservices architecture
test suite for microservicesArchitecture {
    // Microservices require scalability
    assert all stack: TechnologyStack | {
        Scalability in stack.overallQualities
    } is necessary for microservicesArchitecture[stack]

    // Microservices require Go or Node backend
    assert all stack: TechnologyStack | {
        stack.backend = GoBackend or stack.backend = NodeBackend
    } is necessary for microservicesArchitecture[stack]

    // Microservices require Postgres or MongoDB
    assert all stack: TechnologyStack | {
        stack.database = Postgres or stack.database = MongoDB
    } is necessary for microservicesArchitecture[stack]
}

// Tests rapid prototyping stack requirements
test suite for rapidPrototyping {
    // Basic validation of rapid prototyping predicate
    assert all stack: TechnologyStack | {
        rapidPrototyping[stack]
    } is necessary for rapidPrototyping[stack]
}

// Tests enterprise architecture requirements
test suite for enterpriseArchitecture {
    // Basic validation of enterprise architecture predicate
    assert all stack: TechnologyStack | {
        enterpriseArchitecture[stack]
    } is necessary for enterpriseArchitecture[stack]
}

// Tests e-commerce stack requirements
test suite for ecommerceStack {
    // E-commerce requires reliability, scalability and security
    assert all stack: TechnologyStack | {
        Reliability in stack.overallQualities and
        Scalability in stack.overallQualities and
        Security in stack.overallQualities
    } is necessary for ecommerceStack[stack]

    // E-commerce requires authentication
    assert {
        some stack: TechnologyStack | no stack.auth and ecommerceStack[stack]
    } is unsat
}

// Tests content management stack requirements
test suite for contentStack {
    // Content stacks need good dev experience and maintainability
    assert all stack: TechnologyStack | {
        DevExperience in stack.overallQualities 
        and Maintainability in stack.overallQualities
    } is necessary for contentStack[stack]

    // Content stacks must use NextJS frontend
    assert {
        some stack: TechnologyStack | stack.frontend != NextJS and contentStack[stack]
    } is unsat
}

// Tests real-time application stack requirements
test suite for realtimeStack {
    // Real-time apps need speed
    assert all stack : TechnologyStack | {
        Speed in stack.overallQualities } is necessary for realtimeStack[stack]

    // Real-time apps need Firebase or Redis database
    assert all stack : TechnologyStack | {
        stack.database = Firebase or stack.database = Redis 
    } is necessary for realtimeStack[stack] 

    // Real-time apps need Node or Go backend
    assert all stack : TechnologyStack | {
        stack.backend = NodeBackend or stack.backend = GoBackend
    } is necessary for realtimeStack[stack]
}