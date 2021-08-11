# SOFTWARE PRE-REQ
# 
# Julia 1.3.1
# Catlab 0.5.3
# Latex

using Catlab.WiringDiagrams
using Catlab.Doctrines
using Catlab

using Catlab.Graphics
import Catlab.Graphics: Graphviz

import TikzPictures
using Catlab.Graphics

EXAMPLE = "blocksworld";  

# Grab domain, problem, and solution files
DOMAIN_FILEPATH = joinpath("..", "examples", EXAMPLE, "domain.pddl")
PROBLEM_FILEPATH = joinpath("..", "examples", EXAMPLE, "problem.pddl")
SOLUTION_FILEPATH = joinpath("..", "examples", EXAMPLE, "solution.txt")

# Adapted to Julia from https://github.com/pucrs-automated-planning/pddl-parser/blob/master/PDDL.py
using Printf
function scan_tokens(filename)
    file = open(filename) do f
        domain_file = read(f, String)
        stack = []
        list = []
        tokens = eachmatch(r"[()]|[\w\-?:]+", domain_file)
        for tt in tokens
            t = String(tt.match)
            if t == "(" 
                stack = push!(stack, list)
                list = []
            elseif t == ")"
                if length(stack) > 0
                    l = list
                    list = pop!(stack)
                    list = push!(list, l)
                else
                    println("Missing open parentheses!")
                    return []
                end
            else
                list = push!(list, t)
            end
        end
        if length(stack) > 0
            println("Missing closing parentheses!")
            return
        end
        if length(list) != 1
            println("Malformed expressed")
            return
        end
        return list[1]
    end
end

function parse_action(actions, group)
    name = splice!(group, 1)
    
    parameters = []
    pos_pre = []
    neg_pre = []
    add_post = []
    del_post = []
    
    while length(group) > 0
        t = splice!(group, 1)
        if t == ":parameters"
            parameters = []
            untyped_parameters = []
            p = splice!(group, 1)
            while length(p) > 0
                t = splice!(p, 1)
                untyped_parameters = push!(parameters, t)
            end
        elseif t == ":precondition"
            p = splice!(group, 1)
            pos_pre, neg_pre = split_predicates(p, pos_pre, neg_pre)
        elseif t == ":effect"
            p = splice!(group, 1)
            add_post, del_post = split_predicates(p, add_post, del_post)
        end
    end    
    a = Dict("name" => name,
             "parameters" => parameters, 
             "preconditions" => Dict("positive" => pos_pre, 
                                     "negative" => neg_pre),
             "postconditions" => Dict("positive" => add_post,
                                      "negative" => del_post))
    actions = push!(actions, a)
    return actions
end

function parse_predicates(predicates, group)
    for pred in group
        predicate_name = splice!(pred, 1)
        untyped_variables = []
        while length(pred) > 0
            t = splice!(pred, 1)
            untyped_variables = push!(untyped_variables, t)
        end
        predicates[predicate_name] = untyped_variables
    end
    return predicates
end

function split_predicates(group, pos, neg)
    if group[1] == "and"
        group = deleteat!(group, 1)
    else
        group = [group]
    end
    for predicate in group
        if length(predicate) < 1
            return [], []
        end
        if predicate[1] == "not"
            neg = append!(neg, predicate[end])
        else
            pos = append!(pos, predicate)
        end
    end
    return pos, neg
end

using JSON
function parse_domain(domain_filename)
    tokens = scan_tokens(domain_filename)
    if (tokens == nothing) 
        return Dict("name" => "", 
        "predicates" => Dict(), 
        "actions" => Dict())
    end
    splice!(tokens, 1)
    domain_name = "unknown"
    actions = []
    predicates = Dict()
    while length(tokens)>0
        group = splice!(tokens, 1)
        t = splice!(group, 1)
        if t == "domain"
            domain_name = group[1]
        elseif t == ":predicates"
            predicates = parse_predicates(predicates, group)
        elseif t == ":action"
            actions = parse_action(actions, group)
        end
    end
    domain = Dict("name" => domain_name, 
        "predicates" => predicates, 
        "actions" => actions)
    return domain
end

domain = parse_domain(DOMAIN_FILEPATH)
# print(json(domain,4))

function make_objects(predicates)
    port_map = Dict()
    for (name, variables) in predicates
        port_name = name
        for v in variables
            port_name = port_name * "\t" * v
        end
        port_map[name] = Ob(FreeSymmetricMonoidalCategory, port_name)
    end
    return port_map
end
port_map = make_objects(domain["predicates"])

function make_neg_objects(predicates)
    port_map = Dict()
    for (name, variables) in predicates
        port_name = "&not;\t" * name
        for v in variables
            port_name = port_name * "\t" * v
        end
        port_map[name] = Ob(FreeSymmetricMonoidalCategory, port_name)
    end
    return port_map
end
neg_port_map = make_neg_objects(domain["predicates"])

function otimes_ports(conditions, port_map, neg_port_map)
    counter = 1
    
    pos_conditions = conditions["positive"]
    neg_conditions = conditions["negative"]
    
    for c in pos_conditions
        if !occursin("?", c)
            if counter == 1
                global ports = port_map[c]  # shouldn't need to be global
                counter += 1
            else
                global ports = otimes(ports, port_map[c])
            end
        end
    end
    
    for c in neg_conditions
        if !occursin("?", c)
            if counter == 1
                global ports = port_map[c]  # shouldn't need to be global
                counter += 1
            else
                global ports = otimes(ports, neg_port_map[c])
            end
        end
    end
    
    return ports
end

function make_morphisms(actions, port_map, neg_port_map)
    action_map = Dict()
    for act in actions
        name = act["name"]
        
        preconditions = act["preconditions"]
        postconditions = act["postconditions"]

        inputs = otimes_ports(preconditions, port_map, neg_port_map)
        outputs = otimes_ports(postconditions, port_map, neg_port_map)
        
        action_map[name] = Hom(name, inputs, outputs)
    end
    return action_map
end

morphism_map = make_morphisms(domain["actions"], port_map, neg_port_map)

function draw_morphisms(morphism_map, prefix, b_labels)
    for k in keys(morphism_map)
        graph = to_graphviz(morphism_map[k]; labels=b_labels)
        filename = joinpath(@__DIR__, "morphisms", prefix * k * ".dot.svg")
        open(filename, "w") do fp 
            print(fp, Graphviz.run_graphviz(graph, format="svg")) 
        end
        open(filename) do f
           display("image/svg+xml", read(f, String))
        end
    end
end

draw_morphisms(morphism_map, "domain_", true)

using JSON

function parse_problem(problem_filename)
    tokens = scan_tokens(problem_filename)

    splice!(tokens, 1)  # remove "define" token
    
    problem_name = "unknown"
    domain_name = "unknown"
    object_list = []
    init = []
    pos_goal = []
    neg_goal = []
    
    while length(tokens)>0
        group = splice!(tokens, 1)
        t = splice!(group, 1)
        if t == "problem"
            problem_name = group[1]
        elseif t == ":domain"
            domain_name = group[1]
        elseif t == ":objects"
            splice!(group, 1)
            while length(group)>0
                if group[1] == "-"
                    splice!(group, 1)
                    objects[splice!(group, 1)] = object_list
                else
                    push!(object_list, splice!(group, 1))
                end
            end
        elseif t == ":init"  # FIXME: not being found
            while length(group)>0
                state = splice!(group, 1)
                append!(init, state)
            end
        elseif t == ":goal"
            p = splice!(group, 1)
            pos_goal_split, neg_goal_split = split_predicates(p, pos_goal, neg_goal)
            
            if length(pos_goal) > 1
                splice!(pos_goal_split, 1)
            end
            
            if length(neg_goal) > 1
                splice!(neg_goal_split, 1)
            end
            
            # make array of array --> array             
            pos_goal = []
            neg_goal = []
            
            for p in pos_goal_split
                append!(pos_goal, p)
            end
            
            for p in neg_goal_split
                append!(neg_goal, p)
            end
        end
    end
    problem = Dict("problem" => problem_name,
                   "domain" => domain_name,
                   "objects" => object_list,
                   "init" => init,
                   "goal" => Dict("positive" => pos_goal,
                                  "negative" => neg_goal))
    return problem
end

problem = parse_problem(PROBLEM_FILEPATH)
print(json(problem,4))

function group_predicates(tokens, domain_pred)
    predicates = []
    pred = Dict()
    predicate_name = "unknown"
    untyped_variables = []
    while length(tokens)>0
        t = splice!(tokens, 1)
        if !(t in keys(domain_pred))
            push!(untyped_variables, t)
        else
            push!(predicates, pred)
            predicate_name = t
            untyped_variables = []
            pred = Dict()
        end
        pred[predicate_name] = untyped_variables
    end
    push!(predicates, pred)
    splice!(predicates, 1)
    return predicates
end
# action = domain["actions"][1]
# domain_pred = domain["predicates"]
# group_predicates(copy(action["preconditions"]["positive"]), domain_pred)
predicates = group_predicates(copy(problem["init"]), domain_pred)

function parse_solution(pddl_solution_filename, actions, domain_pred)
    count = 0
    pred = Dict()
    morphisms = Dict()
    for line in readlines(pddl_solution_filename)
        wordsr = eachmatch(r"[\w\-?]+\w?", line)
        words = map((x) -> String(x.match), wordsr)
        
        println(line)
        println(wordsr)
        println(words)
        
        action_sol = splice!(words, 1)
        var_sol = words
        
        action = filter((x) -> x["name"]==action_sol, actions)[1]
        action_name = action["name"]
        var_map = Dict(zip(action["parameters"], var_sol))
        
        grouped_pred = Dict("action" => action_name, "preconditions" => Dict(), "postconditions" => Dict())
        grouped_pred["preconditions"]["positive"] = group_predicates(copy(action["preconditions"]["positive"]), domain_pred)
        grouped_pred["preconditions"]["negative"] = group_predicates(copy(action["preconditions"]["negative"]), domain_pred)
        grouped_pred["postconditions"]["positive"] = group_predicates(copy(action["postconditions"]["positive"]), domain_pred)
        grouped_pred["postconditions"]["negative"] = group_predicates(copy(action["postconditions"]["negative"]), domain_pred)
            
        for cond in ["preconditions", "postconditions"]
            b_first_port = true
            v0 = grouped_pred[cond]
            for sign in ["positive", "negative"]
                v1 = v0[sign]
                for p_dict in v1
                    for (var, assgn) in var_map
                        map((x) -> replace!(x, var => assgn), values(p_dict))
                    end
                    
                    if sign == "positive"
                        new_port = make_objects(p_dict)
                    elseif sign == "negative"
                        new_port = make_neg_objects(p_dict)
                    end
  
                    for (name, port) in new_port
                        if b_first_port
                            global ports = port
                            b_first_port = false
                        else
                            global ports = otimes(ports, port)
                        end
                    end
         
                end
            end
            if cond == "preconditions"
                global inputs = ports
            elseif cond == "postconditions"
                global outputs = ports
            end
        end
        pred[string(count)] = grouped_pred
        morphisms[string(count)] = Hom(action_name, inputs, outputs)
        count += 1
    end
    return pred, morphisms
end

domain = parse_domain(DOMAIN_FILEPATH)
solution_predicates, solution_morphisms = parse_solution(SOLUTION_FILEPATH, domain["actions"], domain["predicates"])
draw_morphisms(solution_morphisms, "solution_", true)
# print(json(solution_morphisms,4)) 

function make_all_strings(block, interface)
    if interface == "input"
        f = 2
    elseif interface == "output"
        f = 3
    else
        f = nothing
    end
    
    new_block = []
    for m in block
        if typeof(m) == Catlab.Doctrines.FreeSymmetricMonoidalCategory.Hom{:generator}
            try
                for s in m.args[f].args  # input arguments of morphism
                    push!(new_block, id(s))
                end
            catch
                s = m.args[f]
                push!(new_block, id(s))
            end
        elseif typeof(m) == Catlab.Doctrines.FreeSymmetricMonoidalCategory.Hom{:id} 
            push!(new_block, m)
        elseif typeof(m) == Catlab.Doctrines.FreeSymmetricMonoidalCategory.Hom{:braid}
            for s in m.type_args[f-1].args
                push!(new_block, id(s))
            end
        end
    end
    return new_block
end

function otimes_strings(strings)
    b_first_port = true
    for p in strings
        if b_first_port
            global ports = p
            b_first_port = false
        else
            global ports = otimes(ports, p)
        end
    end
    return ports
end

# import Catlab.Graphics: TikZ

# To convert SVG to PDF or Latex: inkscape --export-type=pdf smc.dot.svg
# Note: inkscape MUST be installed (brew cask install inkscape)

function draw_string_diagram(smc, name, b_labels)
    graph = to_graphviz(smc; labels=b_labels)
#     tikz_doc = to_tikz(smc; labels=b_labels)
#     TikZ.pprint(tikz_doc)
    filename = joinpath(@__DIR__, name * ".dot.svg")
    open(filename, "w") do fp 
        print(fp, Graphviz.run_graphviz(graph, format="svg")) 
    end
    open(filename) do f
       display("image/svg+xml", read(f, String))
    end
end

function bubble_sort_tracking(ls)
    transforms = []
    swaps_exist = true
    while swaps_exist
        swaps_exist = false
        for (i, el) in enumerate(ls)
            if (i + 1 <= length(ls))
                if el < ls[i+1]
                    continue
                elseif el > ls[i+1]
                    push!(transforms, (i, i+1))
                    swaps_exist = true
                    
                    fst = el
                    snd = ls[i+1]
                    ls[i] = snd
                    ls[i+1] = fst
                end
            end
        end
    end
    return transforms
end

function make_problem_blocks(problem, domain_pred)
    # Convert initial and goal state to list of identity morphisms
    
    # Make Initial State Block
    init_pred = group_predicates(copy(problem["init"]), domain_pred)
    init_obj = []
    for p in init_pred
        obj = make_objects(p)
        push!(init_obj, obj)
    end
    init = []
    for o in init_obj
        obj = collect(values(o))[1] # collect returns an array of values
        push!(init, id(obj))
    end
    
    # Make Goal State Block
    grouped_pos = group_predicates(copy(problem["goal"]["positive"]), domain_pred)
    goal_obj = []
    for p in grouped_pos
        obj = make_objects(p)
        push!(goal_obj, obj)
    end
    
    grouped_neg = group_predicates(copy(problem["goal"]["negative"]), domain_pred)
    for p in grouped_neg
        obj = make_objects(p)
        push!(goal_obj, obj)
    end

    goal = []
#     for o in goal_obj
#         obj = collect(values(o))[1] # collect returns an array of values
#         push!(goal, id(obj))
#     end
    
    return init, goal
    
end

init, goal = make_problem_blocks(problem, domain["predicates"])

function backward_pass(curr_block, above_morph)
    above_block = []
    
    if typeof(above_morph) == Catlab.Doctrines.FreeSymmetricMonoidalCategory.Hom{:generator}
        above_strings = make_all_strings([above_morph], "output")
        above_output = above_morph.args[3]
    else
        above_strings = above_morph
        above_output = nothing
    end
    
    println(above_morph)
    
    morph_added = false
    for m in curr_block
        if typeof(m) == Catlab.Doctrines.FreeSymmetricMonoidalCategory.Hom{:generator}  # if generator morphism
            try
                for s in m.args[2].args  # for input arguments of morphism
                    if (above_output != nothing) && (id(s) in above_strings) && (!morph_added)  # if input arg in output of above
                        push!(above_block, above_morph)
                        morph_added = true
                        
                        deleteat!(above_strings, findfirst(x->x==id(s), above_strings)) # update strings accounted for in above strings
                    else
                        push!(above_block, id(s))
                    end
                end
            catch
                s = m.args[2]
                if (above_output != nothing) && (id(s) in above_strings) && (!morph_added)  # if input arg in output of above
                    push!(above_block, above_morph)
                    morph_added = true
                else
                    push!(above_block, id(s))
                end
            end
        elseif typeof(m) == Catlab.Doctrines.FreeSymmetricMonoidalCategory.Hom{:id}  # if identity morphism
            if !(m in above_strings)
                push!(above_block, m)
            else
                if (above_output != nothing) # if above morph is a generator, do not push because it will be handled with morph
                    deleteat!(above_strings, findfirst(x->x==m, above_strings))
                else
                    push!(above_block, m) # if above morph is not a generator, push string, no "hidden" strings
                end
            end
        end
    end
    
    if (!morph_added) && (above_output != nothing)
        push!(above_block, above_morph)
    end
    
    return above_block    
end

function forward_pass(curr_block, below_block)
    
    below_strings = make_all_strings(below_block, "input")
    
    morph_added = false
    for m in curr_block
        if typeof(m) == Catlab.Doctrines.FreeSymmetricMonoidalCategory.Hom{:generator}  # if generator morphism
            try
                for s in m.args[3].args
                    if !(id(s) in below_strings)
                        push!(below_block, id(s))
                    else
                        deleteat!(below_strings, findfirst(x->x==id(s), below_strings))
                    end
                end
            catch
                s = m.args[3]
                if !(id(s) in below_strings)
                        push!(below_block, id(s))
                    else
                        deleteat!(below_strings, findfirst(x->x==id(s), below_strings))
                    end
            end
        elseif typeof(m) == Catlab.Doctrines.FreeSymmetricMonoidalCategory.Hom{:id}  # if identity morphism
            if !(m in below_strings)
                push!(below_block, m)
            else
                deleteat!(below_strings, findfirst(x->x==m, below_strings))
            end
        end
    end
    
end

function bubble_sort_braiding(perm, block)
    blocks = [block]
    
    swaps_exist = true
    while swaps_exist # keep checking for swaps in the current permutation
        swaps_exist = false
        val = make_all_strings(block, "output")
        
        block = []
        skip = -1
        for (i, el) in enumerate(perm) # do one pass through list of permutations
            if (i+1 <= length(perm))
                if i == skip
                    continue
                elseif el < perm[i+1] || swaps_exist # if the current number is less than the adjacent number
                    push!(block, val[i]) # leave value in current position
                elseif el > perm[i+1] # if the current number is greater than the adjacent number
                    swaps_exist = true

                    fst = el        # larger no.
                    snd = perm[i+1] # smaller no.

                    # swap in permutation list
                    perm[i] = snd
                    perm[i+1] = fst

                    # braid and append to result
                    push!(block, braid(val[i].args[1], val[i+1].args[1]))
                    
                    skip = i+1
                end
            elseif i != skip
                push!(block, val[i])
            end
        end
        if swaps_exist == true
            push!(blocks, block)
        end
        
    end
    
    return blocks
end

function add_braids(blocks)
    new_blocks = [] # first block stays the same
    
    for i in 1:length(blocks)-1 # start with the first element of blocks, so previous block can be checked
        curr_block = blocks[i]
        next_block = blocks[i+1]
        
        curr_str = make_all_strings(curr_block, "output")
        next_str = make_all_strings(next_block, "input")
        
        curr_str_perm = []
        
        # For every string in block, find index of matching string in previous block
        for s in curr_str 
            check_ind = 1
            while (check_ind <= length(next_str)  # if there are more strings in the next block to check
                && next_str[check_ind] != s      # if previous string at index doesn't equal current string
                || (check_ind in curr_str_perm))  # if index corresponding to next block was already added
                
                check_ind = check_ind + 1 # increment index to check in previous block
            end
            push!(curr_str_perm, check_ind) # add position of current string in previous block
        end
        
        # track bubble sort for each permutation
        braided_blocks = bubble_sort_braiding(curr_str_perm, curr_block)
        new_blocks = vcat(new_blocks, braided_blocks)
    end
    
    return new_blocks
end

function build_string_diagram(morphisms, problem, domain, b_compose_diagram::Bool)
    n_steps = length(keys(morphisms))-1 # number of steps in PDDL solution
    init, goal = make_problem_blocks(problem, domain["predicates"]) # convert initial and goal state of PDDL to blocks
    
    last_morphism = morphisms[string(n_steps)] # last step in PDDL solution
    
    # Backward pass (weaving input strings from bottom to top)  
    curr_block = goal
    blocks = [curr_block] # instantiate blocks with goal block
    for i in n_steps:-1:-2
        if i < 0
            above_morph = init
        else
            above_morph = morphisms[string(i)]
        end
        curr_block = backward_pass(curr_block, above_morph)
        pushfirst!(blocks, curr_block)
    end
    
    # Forward pass (weaving output strings)
    curr_block = init
    for i in 1:length(blocks)
        below_block = blocks[i]
        forward_pass(curr_block, below_block)
        curr_block = below_block
    end
    
    # Add braids
    blocks = add_braids(blocks)
    
    # Construct SMC
    global smc = nothing
    for (i, b) in enumerate(blocks)
        block = otimes_strings(b)
        if b_compose_diagram
            if smc == nothing
                smc = block
            else
                try
                    smc = compose(smc, block)
                catch
                    println("Failed to connect Block " * string(i-1) * " and Block " * string(i) * "!")
                    draw_string_diagram(smc, "smc_" * string(i), true)

                    smc = block
                end
            end
        else
            draw_string_diagram(block, "block_" * string(i), true)
        end
    end
    draw_string_diagram(smc, "smc", true)
    
    return smc
end
smc = build_string_diagram(solution_morphisms, problem, domain, true)


