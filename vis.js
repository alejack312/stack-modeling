// Technology Stack Architecture Visualization for Sterling

/** Helper to extract the atom from a singleton */
function firstAtomOf(expr) {
    if(!expr.empty())
      return expr.tuples()[0].atoms()[0]
    return 'none'
}
const fam = firstAtomOf // shorthand

/** Extract name without sig prefix */
function getName(atom) {
    if (!atom || atom === 'none') return 'none';
    return atom.toString().split('/').pop();
}

/** Get component from stack field */
function getComponent(stack, fieldName) {
    try {
        const field = instance.field(fieldName);
        const joinResult = stack.join(field);
        
        if (joinResult.empty()) return 'none';
        
        // Get the first tuple's first atom
        return getName(joinResult.tuples()[0].atoms()[0]);
    } catch (e) {
        console.error(`Error in getComponent(${fieldName}):`, e);
        return 'none';
    }
}

/** Get quality set from stack field */
function getQualities(stack, fieldName) {
    try {
        const field = instance.field(fieldName);
        const joinResult = stack.join(field);
        
        if (joinResult.empty()) return [];
        
        // Map all tuples to their quality names
        return joinResult.tuples().map(tuple => {
            return getName(tuple.atoms()[0]);
        }).filter(name => name !== 'none');
    } catch (e) {
        console.error(`Error in getQualities(${fieldName}):`, e);
        return [];
    }
}

/** Get color for technology */
function getTechColor(tech) {
    const colorMap = {
        'NextJS': '#000000',
        'ReactJS': '#61DAFB',
        'Vite': '#646CFF',
        'Angular': '#DD0031',
        'SvelteKit': '#FF3E00',
        'VueJS': '#4FC08D',
        'NodeBackend': '#339933',
        'PythonBackend': '#3776AB',
        'JavaBackend': '#007396',
        'GoBackend': '#00ADD8',
        'RubyBackend': '#CC342D',
        'Postgres': '#336791',
        'SQLDatabase': '#4479A1',
        'MongoDB': '#47A248',
        'Redis': '#DC382D',
        'Firebase': '#FFCA28',
        'PrismaORM': '#2D3748',
        'DrizzleORM': '#8E44AD',
        'OAuth': '#EB5424',
        'JWTAuth': '#000000',
        'FirebaseAuth': '#FFCA28',
        'Auth0': '#EB5424',
        'ClerkAuth': '#6C47FF',
    };
    return colorMap[tech] || '#888888';
}

/** Get color for quality attribute */
function getQualityColor(quality) {
    const colorMap = {
        'Scalability': '#3498db',
        'Speed': '#e74c3c',
        'Reliability': '#2ecc71',
        'Maintainability': '#9b59b6',
        'Security': '#f39c12',
        'DevExperience': '#1abc9c',
        'CostEfficiency': '#34495e',
        'Pedagogy': '#d35400',
    };
    return colorMap[quality] || '#888888';
}

// Get all technology stacks
const stacks = instance.signature('TechnologyStack').atoms();
console.log(stacks)

// Grid configuration for the visualization
const gridConfig = {
    grid_location: { x: 10, y: 10 },
    cell_size: { x_size: 160, y_size: 40 },
    grid_dimensions: {
        y_size: stacks.length * 10, // 10 rows per stack
        x_size: 7 // Components + qualities
    }
};

// Create the grid
const grid = new Grid(gridConfig);

// Populate the grid with stack information
stacks.forEach((stack, stackIndex) => {
  console.log(stack)
    const baseRow = stackIndex * 10;
    
    // Stack header
    grid.add({x: 0, y: baseRow}, new TextBox({
        text: `Stack ${stackIndex + 1}`,
        fontSize: 18,
        fontWeight: 'bold'
    }));
    
    // Component headers
    grid.add({x: 0, y: baseRow + 1}, new TextBox({text: "Component"}));
    grid.add({x: 1, y: baseRow + 1}, new TextBox({text: "Technology"}));
    grid.add({x: 2, y: baseRow + 1}, new TextBox({text: "Qualities"}));
    
    // Get components
    try {
        const frontend = getComponent(stack, 'frontend');
        const backend = getComponent(stack, 'backend');
        const database = getComponent(stack, 'database');
        const orm = getComponent(stack, 'orm');
        const auth = getComponent(stack, 'auth');
        
        // Get qualities
        const frontendBackendQualities = getQualities(stack, 'frontendBackendQualities');
        const backendDatabaseQualities = getQualities(stack, 'backendDatabaseQualities');
        const databaseORMQualities = getQualities(stack, 'databaseORMQualities');
        const authQualities = getQualities(stack, 'authQualities');
        const overallQualities = getQualities(stack, 'overallQualities');
        
        // Frontend row
        grid.add({x: 0, y: baseRow + 2}, new TextBox({text: "Frontend"}));
        grid.add({x: 1, y: baseRow + 2}, new TextBox({
            text: frontend,
            fill: getTechColor(frontend),
            color: 'white',
            padding: 4,
            borderRadius: 4
        }));
        
        // Add frontend qualities
        frontendBackendQualities.forEach((quality, i) => {
            grid.add({x: 2 + i, y: baseRow + 2}, new TextBox({
                text: quality,
                fill: getQualityColor(quality),
                color: 'white',
                padding: 2,
                fontSize: 12,
                borderRadius: 4
            }));
        });
        
        // Backend row
        grid.add({x: 0, y: baseRow + 3}, new TextBox({text: "Backend"}));
        grid.add({x: 1, y: baseRow + 3}, new TextBox({
            text: backend,
            fill: getTechColor(backend),
            color: 'white',
            padding: 4,
            borderRadius: 4
        }));
        
        // Database row
        grid.add({x: 0, y: baseRow + 4}, new TextBox({text: "Database"}));
        grid.add({x: 1, y: baseRow + 4}, new TextBox({
            text: database,
            fill: getTechColor(database),
            color: 'white',
            padding: 4,
            borderRadius: 4
        }));
        
        // Add backend-database qualities
        backendDatabaseQualities.forEach((quality, i) => {
            grid.add({x: 2 + i, y: baseRow + 3.5}, new TextBox({
                text: quality,
                fill: getQualityColor(quality),
                color: 'white',
                padding: 2,
                fontSize: 12,
                borderRadius: 4
            }));
        });
        
        // ORM row (if present)
        if (orm && orm !== 'none') {
            grid.add({x: 0, y: baseRow + 5}, new TextBox({text: "ORM"}));
            grid.add({x: 1, y: baseRow + 5}, new TextBox({
                text: orm,
                fill: getTechColor(orm),
                color: 'white',
                padding: 4,
                borderRadius: 4
            }));
            
            // Add ORM qualities
            databaseORMQualities.forEach((quality, i) => {
                grid.add({x: 2 + i, y: baseRow + 5}, new TextBox({
                    text: quality,
                    fill: getQualityColor(quality),
                    color: 'white',
                    padding: 2,
                    fontSize: 12,
                    borderRadius: 4
                }));
            });
        }
        
        // Auth row (if present)
        if (auth && auth !== 'none') {
            grid.add({x: 0, y: baseRow + 6}, new TextBox({text: "Authentication"}));
            grid.add({x: 1, y: baseRow + 6}, new TextBox({
                text: auth,
                fill: getTechColor(auth),
                color: 'white',
                padding: 4,
                borderRadius: 4
            }));
            
            // Add Auth qualities
            authQualities.forEach((quality, i) => {
                grid.add({x: 2 + i, y: baseRow + 6}, new TextBox({
                    text: quality,
                    fill: getQualityColor(quality),
                    color: 'white',
                    padding: 2,
                    fontSize: 12,
                    borderRadius: 4
                }));
            });
        }
        
        // Overall qualities header
        grid.add({x: 0, y: baseRow + 7.5}, new TextBox({
            text: "Overall Qualities",
            fontWeight: 'bold'
        }));
        
        // Overall qualities
        overallQualities.forEach((quality, i) => {
            grid.add({x: i, y: baseRow + 8.5}, new TextBox({
                text: quality,
                fill: getQualityColor(quality),
                color: 'white',
                padding: 4,
                fontSize: 14,
                borderRadius: 4
            }));
        });
    } catch (e) {
        grid.add({x: 0, y: baseRow + 2}, new TextBox({
            text: `Error: ${e.message}`,
            color: 'red'
        }));
    }
});

// Finally, render everything
const stage = new Stage();
stage.add(grid);
stage.render(svg);