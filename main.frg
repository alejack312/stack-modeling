#lang forge

option run_sterling "vis.js"

// =============================================================================
// Component Hierarchy: abstract signatures for our software stack
// =============================================================================

abstract sig Boolean {}
one sig True, False extends Boolean {}

abstract sig Component {}

abstract sig Frontend, Backend, Database, ORM, Authorization  extends Component {}


// =============================================================================
// Specific Technology Instances
// =============================================================================
one sig NextJS, ReactJS, Vite, Angular, SvelteKit, VueJS extends Frontend {}     // Next.js frontend


one sig PythonBackend, NodeBackend, JavaBackend, GoBackend, RubyBackend extends Backend {}    // e.g. a Python-based backend


one sig Postgres, SQLDatabase, MongoDB, Redis, Firebase extends Database {}  // e.g. Postgres SQL database


one sig PrismaORM, DrizzleORM extends ORM {}         // e.g. Prisma ORM x

one sig OAuth, FirebaseAuth, JWTAuth, Auth0, ClerkAuth extends Authorization {} // e.g. OAuth-based auth




sig Compatibility {
  tech1: one Component, 
  tech2: one Component,
  compatible: one Boolean
}

// =============================================================================
// Quality Attributes
// =============================================================================
abstract sig Quality {}
one sig Scalability, Speed, Reliability, Maintainability, Security, 
DevExperience, CostEfficiency, Pedagogy extends Quality {}

// Comprehensive Technology Stack definition
sig TechnologyStack {
    // Components
    frontend: one Frontend,
    backend: one Backend,
    database: one Database,
    orm: one ORM,
    auth: lone Authorization,  // Authentication is optional
    
    // Quality attributes for each pairing
    frontendBackendQualities: set Quality,
    backendDatabaseQualities: set Quality,
    databaseORMQualities: set Quality,
    authQualities: set Quality,
    
    // Overall qualities of the stack
    overallQualities: set Quality
}


// =============================================================================
// Compatibility Constraints
// =============================================================================

// Define the compatibility between technologies
pred isFullStackCompatible[t : TechnologyStack] {
    // Frontend-Backend compatibility
    (some c: Compatibility | {
        c.tech1 = t.frontend and c.tech2 = t.backend and c.compatible = True
    }) and

    // Frontend-Database compatibility
    (some c: Compatibility | {
        c.tech1 = t.frontend and c.tech2 = t.database and c.compatible = True
    })and

    // Frontend-ORM compatibility
    (some c: Compatibility | {
        c.tech1 = t.frontend and c.tech2 = t.orm and c.compatible = True
    }) and

    // Frontend-Authorization compatibility
    (some c: Compatibility | {
          c.tech1 = t.frontend and c.tech2 = t.auth and c.compatible = True
    }) and

    // Backend-Database compatibility
    (some c: Compatibility | {
        c.tech1 = t.backend and c.tech2 = t.database and c.compatible = True
    }) and

    // Backend-ORM compatibility
    (some c: Compatibility | {
        c.tech1 = t.backend and c.tech2 = t.orm and c.compatible = True
    }) and

    // Backend-Authorization compatibility
    (some c: Compatibility | {
        c.tech1 = t.backend and c.tech2 = t.auth and c.compatible = True
    }) and

    // Database-ORM compatibility
    (some c: Compatibility | {
        c.tech1 = t.database and c.tech2 = t.orm and c.compatible = True
    }) 

    // Database-Authorization compatibility

    // Do not need to be compatible with each other as they do not interact directly
    // (some c: Compatibility | {
    //     c.tech1 = t.database and c.tech2 = t.auth and c.compatible = True
    // }) and

    // ORM-Authorization compatibility 
    
    // Do not need to be compatible with each other as they do not interact directly 
    // (some c: Compatibility | {
    //     c.tech1 = t.orm and c.tech2 = t.auth and c.compatible = True
    // })
}

pred basicCompatibility {
    // Compatibility is symmetric: if (A,B) is True, so is (B,A)
    all c: Compatibility | {

        c.compatible = True implies {

            some c2: Compatibility | {
                c2.tech1 = c.tech2 and c2.tech2 = c.tech1 and c2.compatible = True
            }
        }
    }

    // No tech is incompatible with itself: (T,T) must always be True
    all t: Component | 
        some c: Compatibility | 
            c.tech1 = t and c.tech2 = t and c.compatible = True
}


// =============================================================================
// Graphical Properties of the Technology Stack
// =============================================================================



// =============================================================================
// Quality Attributes and their implications
// =============================================================================

pred exampleStack {
    // Define frontend-backend pairing
    some t : TechnologyStack | {
        t.frontend = NextJS
        t.backend = NodeBackend
        t.database = Postgres
        t.orm = PrismaORM
        t.frontendBackendQualities = (Speed + DevExperience)
        t.backendDatabaseQualities = (Scalability + Reliability)
        t.databaseORMQualities = (Maintainability + DevExperience + Reliability + Speed)
        t.authQualities = (Security + DevExperience)
    }
}

// =============================================================================
// (Optional) Additional Constraints
// =============================================================================


// Check that no stack optimizes for all qualities
pred allQualitiesImpossible {
    no stack: TechnologyStack | stack.overallQualities = Quality
} 

// Constraints for a valid stack
pred validStacks {
    all stack : TechnologyStack | {
        // Each stack must have a frontend, backend, and database
        one stack.frontend
        one stack.backend
        one stack.database
        
        // If there is an ORM, it must be paired with a database
        no stack.orm implies no stack.database
        stack.database = Firebase implies no stack.orm   

        // All authorization must have security as a quality
        some stack.auth implies Security in stack.authQualities
    }

    // Each stack must have at least one quality attribute
    all stack : TechnologyStack | {
        some stack.frontendBackendQualities
        some stack.backendDatabaseQualities
        some stack.databaseORMQualities
        some stack.auth implies some stack.authQualities
    }

    // Each stack must have an overall quality attribute
    all stack : TechnologyStack | {
        some stack.overallQualities
        allQualitiesImpossible
    }    
}

// Add this predicate to define quality implications for all technologies
pred technologyQualityImplications {
    all stack: TechnologyStack | {
        // Frontend quality implications
        stack.frontend = NextJS implies (Speed + DevExperience) in stack.frontendBackendQualities
        stack.frontend = Vite implies (Pedagogy + CostEfficiency) in stack.frontendBackendQualities
        stack.frontend = SvelteKit implies (DevExperience + Speed) in stack.frontendBackendQualities
        stack.frontend = ReactJS implies (Scalability + DevExperience) in stack.frontendBackendQualities
        
        // Backend quality implications
        stack.backend = NodeBackend implies Speed in stack.backendDatabaseQualities
        stack.backend = PythonBackend implies Maintainability in stack.backendDatabaseQualities
        stack.backend = GoBackend implies (Speed + Scalability) in stack.backendDatabaseQualities
        
        // Database quality implications
        stack.database = Postgres implies (Reliability + Maintainability) in stack.backendDatabaseQualities
        stack.database = MongoDB implies Scalability in stack.backendDatabaseQualities
        stack.database = Redis implies Speed in stack.backendDatabaseQualities

        stack.database = Firebase implies {
            Speed in stack.backendDatabaseQualities
            CostEfficiency in stack.backendDatabaseQualities
            Pedagogy in stack.backendDatabaseQualities
            Security not in stack.backendDatabaseQualities  // Firebase is not secure
        }
        
        // ORM quality implications
        stack.orm = DrizzleORM implies Speed in stack.databaseORMQualities
        stack.orm = PrismaORM implies (Reliability + DevExperience) in stack.databaseORMQualities
        
        // Auth quality implications
        stack.auth = JWTAuth implies (Speed + CostEfficiency) in stack.authQualities
        stack.auth = OAuth implies Security in stack.authQualities
        stack.auth = ClerkAuth implies (DevExperience + Security) in stack.authQualities
    }
}

// Add this predicate to define quality tradeoffs
pred qualityTradeoffs {
    all stack: TechnologyStack | {
        // Speed vs Reliability tradeoff
        #(Speed & stack.overallQualities) > 2 implies 
            #(Reliability & stack.overallQualities) < 2
            
        // DevExperience vs Maintainability tradeoff
        #(DevExperience & stack.overallQualities) > 2 implies
            #(Maintainability & stack.overallQualities) < 2
            
        // Pedagogy limits other qualities
        Pedagogy in stack.overallQualities implies
            #(stack.overallQualities & (Speed + Scalability)) < 2
            
        // Security has performance costs
        #(Security & stack.overallQualities) > 1 implies
            #(Speed & stack.overallQualities) < 2

        // Firebase reduces overall security
        stack.database = Firebase implies 
            #(Security & stack.overallQualities) <= 1
    }
}

// Add a constraint that limits the maximum qualities a stack can have
pred qualityBudget {
    all stack: TechnologyStack | {
        // You can't optimize for everything
        #stack.overallQualities <= 6
        
        // Each component pairing can have at most 3 qualities
        #stack.frontendBackendQualities <= 3
        #stack.backendDatabaseQualities <= 3
        #stack.databaseORMQualities <= 3
        #stack.authQualities <= 2
    }
}

// Define a predicate to propagate qualities from components to the overall stack
pred qualityPropagation {
    all stack: TechnologyStack | {
        stack.overallQualities = stack.frontendBackendQualities + 
        stack.backendDatabaseQualities + stack.databaseORMQualities + 
        stack.authQualities
    }
}

// Define technology combinations that don't work well together
pred technologyConflicts {
    all stack: TechnologyStack | {
        // Vite's pedagogical approach conflicts with enterprise-grade database
        stack.frontend = Vite implies stack.database != Postgres
        stack.frontend = Vite implies stack.database != SQLDatabase
        
        // Fast backends and reliable databases have integration challenges
        (stack.backend = NodeBackend or stack.backend = GoBackend) and 
        stack.database = Postgres implies 
            not (Speed in stack.backendDatabaseQualities and 
                 Reliability in stack.backendDatabaseQualities)
    }
}

// Predicate to find stacks optimized for specific qualities
pred optimizedFor[desiredQualities: set Quality, stack: TechnologyStack] {
    // Make sure all desired qualities are included in the stack's overall qualities
    desiredQualities in stack.overallQualities
    
    // In optimizedFor predicate
    #(desiredQualities & (stack.frontendBackendQualities 
        + stack.backendDatabaseQualities 
        + stack.databaseORMQualities)) >= #desiredQualities
    
    // If auth is present, it should also contribute to the desired qualities
    some stack.auth implies #(desiredQualities & stack.authQualities) > 0
}



// Predicate for microservices architecture
pred microservicesArchitecture[stack: TechnologyStack] {
    // Microservices typically prioritize scalability
    Scalability in stack.overallQualities
    
    // Favor certain technologies that work well in microservices
    stack.database = Postgres or 
    stack.database = MongoDB
    
    // Node or Go backends typically work well for microservices
    stack.backend = NodeBackend or
    stack.backend = GoBackend
}

// Predicate for rapid prototyping architecture
pred rapidPrototyping[stack: TechnologyStack] {
    // Rapid prototyping values development experience and speed
    DevExperience in stack.overallQualities
    Speed in stack.overallQualities
    
    // NextJS or SvelteKit are great for rapid development
    stack.frontend = NextJS or 
    stack.frontend = SvelteKit
    
    // Prisma provides type safety and rapid development
    stack.orm = PrismaORM
}

// Predicate for enterprise-grade architecture
pred enterpriseArchitecture[stack: TechnologyStack] {
    // Enterprise solutions value reliability and security
    Reliability in stack.overallQualities
    Security in stack.overallQualities
    
    // Postgres is often preferred for enterprise
    stack.database = Postgres
    
    // Must have authentication
    some stack.auth
}

// E-commerce optimized stack
pred ecommerceStack[stack: TechnologyStack] {
    // E-commerce needs reliability, scalability, and security
    Reliability in stack.overallQualities
    Scalability in stack.overallQualities
    Security in stack.overallQualities
    
    // Needs robust database
    stack.database = Postgres or stack.database = MongoDB
    
    // Must have authentication
    some stack.auth
}

// Content-focused applications (blogs, news sites)
pred contentStack[stack: TechnologyStack] {
    // Content sites need good developer experience and maintainability
    DevExperience in stack.overallQualities
    Maintainability in stack.overallQualities
    
    // Next.js is great for content sites with SSR/SSG
    stack.frontend = NextJS
}

// Real-time applications (chat, live dashboards)
pred realtimeStack[stack: TechnologyStack] {
    // Real-time apps need speed
    Speed in stack.overallQualities
    
    // Redis is great for real-time data
    stack.database = Redis or stack.database = Firebase
    
    // Node or Go are good for real-time processing
    stack.backend = NodeBackend or stack.backend = GoBackend
}

// =============================================================================
// Stack Evolution
// =============================================================================

// Model how a stack might evolve over time
pred evolutionPath[initial: TechnologyStack, evolved: TechnologyStack] {
    // Keep the same frontend for continuity
    initial.frontend = evolved.frontend
    
    // Database might be upgraded for scaling
    (initial.database = MongoDB and evolved.database = Postgres) or
    (initial.database = Firebase and evolved.database = MongoDB) or
    initial.database = evolved.database
    
    // Quality improvements
    #evolved.overallQualities > #initial.overallQualities
    Reliability in evolved.overallQualities
    Security in evolved.overallQualities
}

run {
    validStacks
    qualityPropagation
    technologyQualityImplications
    qualityTradeoffs
    qualityBudget
    
    some stack: TechnologyStack | optimizedFor[(Speed + Scalability), stack]
} for 1 TechnologyStack

// Find a stack that balances speed and reliability
run {
    validStacks
    qualityPropagation
    technologyQualityImplications
    qualityTradeoffs
    qualityBudget
    
    some stack: TechnologyStack | {
        Speed in stack.overallQualities
        Reliability in stack.overallQualities
    }
} for 1 TechnologyStack

// Find a highly educational stack (pedagogical)
run {
    validStacks
    qualityPropagation
    technologyQualityImplications
    qualityTradeoffs
    qualityBudget
    
    some stack: TechnologyStack | {
        Pedagogy in stack.overallQualities
        stack.frontend = Vite
    }
} for 1 TechnologyStack

// Run statement for finding a microservices architecture
run {
    validStacks
    qualityPropagation
    technologyQualityImplications
    qualityTradeoffs
    qualityBudget
    
    some stack: TechnologyStack | microservicesArchitecture[stack]
} for 1 TechnologyStack

// Run statement for rapid prototyping stack
run {
    validStacks
    qualityPropagation
    technologyQualityImplications
    qualityTradeoffs
    qualityBudget
    
    some stack: TechnologyStack | rapidPrototyping[stack]
} for 1 TechnologyStack

// Run statement for enterprise-grade architecture
run {
    validStacks
    qualityPropagation
    technologyQualityImplications
    qualityTradeoffs
    qualityBudget
    
    some stack: TechnologyStack | enterpriseArchitecture[stack]
} for 1 TechnologyStack

// Run statement for e-commerce optimized stack
run {
    validStacks
    qualityPropagation
    technologyQualityImplications
    qualityTradeoffs
    qualityBudget
    
    some stack: TechnologyStack | ecommerceStack[stack]
} for 1 TechnologyStack

// Run statement for content-focused applications
run {
    validStacks
    qualityPropagation
    technologyQualityImplications
    qualityTradeoffs
    qualityBudget
    
    some stack: TechnologyStack | contentStack[stack]
} for 1 TechnologyStack

// Run statement for real-time applications
run {
    validStacks
    qualityPropagation
    technologyQualityImplications
    qualityTradeoffs
    qualityBudget
    
    some stack: TechnologyStack | realtimeStack[stack]
} for 1 TechnologyStack

// Run statement for stack evolution
run {
    validStacks
    qualityPropagation
    technologyQualityImplications
    qualityTradeoffs
    qualityBudget
    
    some initial, evolved: TechnologyStack | 
        initial != evolved and evolutionPath[initial, evolved]
} for exactly 2 TechnologyStack