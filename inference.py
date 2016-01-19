#TO-DO return false if certain key is not there in kb --done
# return false if proper combination does not exist --done
#return false if query arguments number do not match with consequents --done
#you should not replace predicate values same as of variable occurence --done
# writing files to output file --done

# importing libraries
import sys
import re
import itertools

#reading input from command prompt and creating output file to be written
input_file=sys.argv[2]
input_data=open(input_file,"r")
input_lines=input_data.readlines()
output=open("output.txt",'w')

query_numbers=int(input_lines[0])
query_list=[]
knowledge_base=[]

#creating list of query and knowledge base
for i in range(1,query_numbers+1):
    query_list.append(input_lines[i].strip())
for i in range(query_numbers+2,len(input_lines)):
    knowledge_base.append(input_lines[i].strip().replace(" ",""))
#print query_list
#print knowledge_base
    
#create dictionary
knowledge_structure={}
set_constants = set()
pattern_for_args = r'\(([A-Za-z,]+)\)'
    
#getting predicates and knowledge structure
for i in knowledge_base:
    #split on "=>"
    kb_split=i.split("=>")
    
    if "=>" in i:
        j=kb_split[1] # the entire clause part of consequent
        predicate=j[:j.index("(")]
        
        if predicate not in knowledge_structure:
            knowledge_structure[predicate]=[[],[],[]]
            list_args=str(re.findall(pattern_for_args,j)).split(",")
            knowledge_structure[predicate][2].append(len(list_args))
        knowledge_structure[predicate][1].append(i)
    else:
        j=kb_split[0] #if the clause is a fact
        
        predicate=j[:j.index("(")]
        print predicate
        if predicate not in knowledge_structure:
            knowledge_structure[predicate]=[[],[],[]]
            list_args=str(re.findall(pattern_for_args,j)).split(",")
            knowledge_structure[predicate][2].append(len(list_args))
        knowledge_structure[predicate][0].append(i)
    pattern_for_variable = r'\(([A-Za-z,]+)\)'
    list_constant = re.findall(pattern_for_variable,i)
    for c in list_constant:
        arguments = c.split(',')
        for a in arguments:
            if not a[0].islower():
                set_constants.add(a)

# unification method
def unification(set_variable,set_constant,rhs_substitution):
    #print set_constant
    length_of_permutations=abs(len(set_variable)-len(rhs_substitution))
    variables = list(set_variable-set(rhs_substitution.keys()))
    permutations= list(itertools.product(set_constant,repeat=length_of_permutations))
    list_unified = []
    for p in permutations:
        list_unified.append(dict(zip(variables,p)+rhs_substitution.items()))
    #print list_unified
    return list_unified
    
# backward chaining method

def backward_chaining(kb,query):
    #print query
    global ocount
    ocount=0
    global final_result
    final_result=""
    if query in list_visited_queries:
        #list_visited_queries.remove(query)
        #print "visited"
        ocount+=1
        return "FALSE"
    #print query
    list_visited_queries.append(query)
    query_predicate=query[:query.index("(")]
    if query_predicate not in kb.keys():
        ocount+=1
        #list_visited_queries.remove(query)
        return "FALSE"
    facts=kb[query_predicate][0]
    #print facts
    if facts:
        #print "facts"
        #list_visited_queries.remove(query)
        if query in facts:
            #list_visited_queries.remove(query)
            return "TRUE"
        else:
            ocount += 1
            final_result= "FALSE"
            #return "FALSE"
    
    # defining pattern and getting arguments of query
    pattern_for_variable = r'\(([A-Za-z,]+)\)'
    list_of_query_arguments = re.findall(pattern_for_variable,query)[0].split(',')
    #print list_of_query_arguments
    #check if query_arguments are equal to the arguments of predicates in the kb
    if len(list_of_query_arguments)!=kb[query_predicate][2][0]:
        ocount+=1
        #list_visited_queries.remove(query)
        return "FALSE"
        
    # check all the clauses that have same predicate
    for i in kb[query_predicate][1]:
    # split to get lhs and rhs
        clause_split=i.split("=>")
        clause_lhs=clause_split[0]
        clause_rhs=clause_split[1]  
        
    # split to get each expression in lhs
        lhs_and=clause_lhs.split("^")
    
    #define a pattern to get list of arguments which could be constants+variables
        #pattern_for_variable = r'\(([A-Za-z,]+)\)'
        list_of_arguments = re.findall(pattern_for_variable,i)
        list_of_rhs_arguments = re.findall(pattern_for_variable,clause_rhs)[0].split(",")
        #creating a list of variables and constants
        set_variables=set()
        #list_constants=set()
        for j in list_of_arguments:
            final_list_arguments=j.split(",")
            for k in final_list_arguments:
                if k[0].islower():
                    set_variables.add(k)
                #else:
                #    list_constants.add(k)
        #print list_of_query_arguments
        #print list_of_rhs_arguments
        rhs_substitution={}
        arg_no=0
        for rh in list_of_rhs_arguments:
            #print rh
            #print set_constants
            if rh in set_constants:
                if rh==list_of_query_arguments[arg_no]:
                    #rhs_substitution[rh]=rh
                    arg_no+=1
                else:
                    ocount+=1
                    return "FALSE"
            else:
                if rh in rhs_substitution:
                    #print arg_no
                    #print list_of_rhs_arguments[arg_no]
                    #print rhs_substitution[rh]
                    if list_of_query_arguments[arg_no]!=rhs_substitution[rh]:
                        ocount+=1
                        return "FALSE"
                rhs_substitution[rh]=list_of_query_arguments[list_of_rhs_arguments.index(rh)]
                arg_no+=1
        #rhs_substitution=dict(zip(list_of_rhs_arguments,list_of_query_arguments))
        
        #print rhs_substitution
    # unify
        list_all_unified=unification(set_variables,set_constants,rhs_substitution)
        #print list_all_unified,query
    # pass matching unified values to rest
    # check for a correct unification combination for first expression
        global count
        for u in list_all_unified:
            #list_visited_queries=[]
            #print"---",u
            count=0 
            for c in lhs_and:                    
                query1=c 
                                   
                for key in u:
                    qpredicate=query1[:query1.index("(")]
                    qargs=query1[query1.index("(")+1:query1.index(")")].split(",")
                    qargs=[u[key] if k==key else k for k in qargs]
                    query1=qpredicate+"("+",".join(str(a) for a in qargs)+")"
                
                result=backward_chaining(knowledge_structure,query1)
                #print query1,result
                if result=="FALSE":
                    if query1 in list_visited_queries:
                        list_visited_queries.remove(query1)
                        #print "removed",query1
                    #print "break"
                    count += 1
                    break
                else:
                    if query1 in list_visited_queries:
                        list_visited_queries.remove(query1)
                        #print "else removed",query1
                    #list_visited_queries.remove(query1)
            #print count
            #print ocount
            if count!=0 or ocount!=0:    
                final_result= "FALSE"
                #return final_result
    # if backward chaining of that is true
        #check for rest of expressions with same unified dict
            else:
                final_result= "TRUE"
                #print "result returned"
                return final_result                
    return final_result
for queries in query_list:
    #list of queries that i have visited
    list_visited_queries=[]
    inference = backward_chaining(knowledge_structure,queries)
    output.write(str(inference))
    output.write("\n")
output.close()
#print backward_chaining(knowledge_structure,"H(John)")