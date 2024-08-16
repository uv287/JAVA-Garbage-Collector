import java.util.*;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentLinkedQueue;
import java.util.stream.Collectors;

import com.google.common.graph.Graph;

import soot.*;
import soot.baf.StaticInvokeInst;
import soot.jimple.AssignStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.ReturnStmt;
import soot.jimple.Jimple;
import soot.jimple.ParameterRef;
import soot.jimple.StaticInvokeExpr;
import soot.jimple.ThisRef;
import soot.jimple.internal.*;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;
import soot.toolkits.graph.*;
import soot.toolkits.scalar.SimpleLiveLocals;
import soot.toolkits.scalar.LiveLocals;


public class AnalysisTransformer extends SceneTransformer {
    static CallGraph cg;

    static Map<Integer, Set<String>> graph = new ConcurrentHashMap<>();
    static Map<Set<String>, Set<Integer>> Heap = new ConcurrentHashMap<>();
    static Queue<Integer> queue = new ConcurrentLinkedQueue<>();
    static Queue<Integer> queueR = new ConcurrentLinkedQueue<>();

    static Map<Integer, Integer> GC_line_no = new ConcurrentHashMap<>();
    static Map<String, Set<Integer>> method_GC = new ConcurrentHashMap<>();
    static Map<String, Set<String>> parameter = new ConcurrentHashMap<>();
    static Map<String, String> parentMethod = new ConcurrentHashMap<>();
    static Map<String, String> returnstmt_parMap = new ConcurrentHashMap<>();

    TreeMap<String, Set<String>> ans = new TreeMap<>();
    
    @Override
    protected void internalTransform(String arg0, Map<String, String> arg1) {
        Set<SootMethod> methods = new LinkedHashSet <>();
        cg = Scene.v().getCallGraph();

        // Get the main method
        SootMethod mainMethod = Scene.v().getMainMethod();

        getlistofMethods(mainMethod, methods);

        processCFG(mainMethod);

        for (SootMethod method : methods)
        {
            String className = method.getDeclaringClass().getName();
            String methodName = method.getName();

            if(!methodName.equals("<init>"))
            {
                String ans_key = className+":"+methodName;
                Set<Integer> gc_val = method_GC.get(methodName);

                TreeSet<String> ans_set = new TreeSet<>();

                for(Integer line_num : gc_val)
                {
                    if(line_num >0)
                    {
                        String set_val = line_num.toString()+":"+GC_line_no.get(line_num).toString();
                        ans_set.add(set_val);
                    }
                }
                ans.put(ans_key, ans_set);
            } 
        }

        for (Map.Entry<String, Set<String>> entry : ans.entrySet()) 
        {
            String key = entry.getKey();
            Set<String> values = entry.getValue();

            System.out.print(key);
            for (String value : values)
            {
                System.out.print(" " + value);
            }
            System.out.println();
        }


    }
    
    private static void getlistofMethods(SootMethod method, Set<SootMethod> reachableMethods) {
        // Avoid revisiting methods
        if (reachableMethods.contains(method)) {
            return;
        }
        // Add the method to the reachable set
        reachableMethods.add(method);

        Set<Integer> collected = new HashSet<Integer>();
        method_GC.put(method.getName(), collected);

        // Iterate over the edges originating from this method
        Iterator<Edge> edges = Scene.v().getCallGraph().edgesOutOf(method);

        while (edges.hasNext()) {
            Edge edge = edges.next();
            SootMethod targetMethod = edge.tgt();
            // Recursively explore callee methods
            if (!targetMethod.isJavaLibraryMethod()) {
                getlistofMethods(targetMethod, reachableMethods);
            }
        }
    }

    protected static void processCFG(SootMethod method) {
        if(method.toString().contains("init")  ) { return; }
        Body body = method.getActiveBody();
        // Get the callgraph 
        UnitGraph cfg = new BriefUnitGraph(body);
        // Get live local using Soot's exiting analysis
        LiveLocals liveLocals = new SimpleLiveLocals(cfg);
        // Units for the body
        PatchingChain<Unit> units = body.getUnits();
        // System.out.println("\n-----" + body.getMethod().getName() + "-----");

        String methodName = body.getMethod().getName();
        for (Unit u : units) 
        {
            // System.out.println("Unit: " + u);
            List<Local> before = liveLocals.getLiveLocalsBefore(u);
            List<Local> after = liveLocals.getLiveLocalsAfter(u);
            // System.out.println("Live locals before: " + before);
            // System.out.println("Live locals after: " + after);
            // // System.out.println();

            

            if(u instanceof AssignStmt)
            {

                AssignStmt stmt = (AssignStmt) u;
                Value rightOp = stmt.getRightOp();

                //Handle the New expression statement
                if(rightOp instanceof JNewExpr)
                {
                    int obj_line = u.getJavaSourceStartLineNumber();
                    String lhs= stmt.getLeftOp().toString();
                    lhs = lhs + "." + methodName;
                    
                    if(graph.containsKey(obj_line))
                    {
                        graph.get(obj_line).add(lhs);
                    }
                    else
                    {
                        Set<String> valueSet1 = new HashSet<>();
                        valueSet1.add(lhs);
                        graph.put(obj_line, valueSet1);
                    }

                    GC_line_no.put(obj_line,-1);
                }

                else
                {
                    Value lhs= stmt.getLeftOp();
                    //check that if the left side of the value is reference variable or not
                    if(lhs.getClass().toString().equals("class soot.jimple.internal.JInstanceFieldRef"))
                    {
                        //String slicing part

                        String[] parts = lhs.toString().split("\\."); // Split the string at the dot (.)
                                
                        String baseReference = parts[0]; 
                        String fieldNameWithTypeInfo = parts[1]; 

                        String fieldName = fieldNameWithTypeInfo.split(" ")[2];
                        fieldName = fieldName.substring(0, fieldName.length() - 1);

                        Integer main_key = new Integer(0);


                        //findout the rhs value object and add the lhs into that
                        for (Map.Entry<Integer, Set<String>> entry : graph.entrySet()) 
                        {
                            Integer key = entry.getKey();
                            Set<String> values = entry.getValue();

                            if (values.contains(rightOp.toString()+"."+methodName)) {
                                values.add(lhs.toString()+"." + methodName);
                                graph.put(key, values);
                                main_key = key;
                            }  
                        }

                        //if lefthand side of the assignement statement is reference variable and base refrences are parameters or not
                        
                        if(parameter.containsKey(methodName))
                        {
                            // System.out.println("Hello");
                            Set<String> set_of_paramter = parameter.get(methodName);
                            if(set_of_paramter.contains(baseReference))
                            {
                                // System.out.println("Hello");   
                                String Parent_methodName = parentMethod.get(methodName);
                                for (Map.Entry<Integer, Set<String>> entry : graph.entrySet()) 
                                {
                                    Set<String> values = entry.getValue();

                                    if(values.contains(baseReference+"."+methodName))
                                    {
                                        // System.out.println("Hello");   
                                        Set<String> parents_update = graph.get(main_key);
                                        for(String v : values)
                                        {
                                            String[] prts = v.split("\\.");
                                            // System.out.println("1 : "+prts[0] + " 2 : "+ prts[1] ); 
                                            if(prts.length==2 && prts[1].equals(Parent_methodName))
                                            {
                                                // System.out.println(v);   
                                                parents_update.add(prts[0]+"."+fieldNameWithTypeInfo+"."+prts[1]);
                                            }
                                        }
                                    }
                                }


                            }
                        }


                        // System.out.println("Out of loop");
                        for (Map.Entry<Integer, Set<String>> entry : graph.entrySet()) 
                        {
                            // System.out.println("In of loop");
                            Integer key = entry.getKey();
                            Set<String> values = entry.getValue();

                            if (values.contains(baseReference+"."+methodName)) {
                                Set<String> keySet = new HashSet<String>();
                                Set<Integer> valueSet = new HashSet<Integer>();
                                keySet.add(key.toString());
                                keySet.add(fieldName);

                                if(Heap.containsKey(keySet))
                                {
                                    Heap.get(keySet).add(key);
                                }
                                else
                                {
                                    valueSet.add(main_key);
                                    Heap.put(keySet, valueSet);
                                }

                            }  
                        }
                    }

                    else if (!(rightOp instanceof InvokeExpr))
                    {
                        int found = 0;
                        for (Map.Entry<Integer, Set<String>> entry : graph.entrySet()) 
                        {
                            Integer key = entry.getKey();
                            Set<String> values = entry.getValue();

                            if (values.contains(rightOp.toString()+"."+methodName)) {
                                found= 1;
                                values.add(lhs.toString()+"."+methodName);
                                graph.put(key, values);
                            }  
                            
                        }
                        
                        //handel that case where register assign the value to parmeter field refrence or this pointer field refernce
                        if(found == 0)
                        {
                            //String slicing part

                            String[] parts = rightOp.toString().split("\\."); // Split the string at the dot (.)
                                
                            String baseReference = parts[0]; 
                            String fieldNameWithTypeInfo = parts[1]; 

                            String fieldName = fieldNameWithTypeInfo.split(" ")[2];
                            fieldName = fieldName.substring(0, fieldName.length() - 1); 
                            
                            Integer base_key = new Integer(0);

                            //findout base refence object
                            for (Map.Entry<Integer, Set<String>> entry : graph.entrySet()) 
                            {
                                Integer key = entry.getKey();
                                Set<String> values = entry.getValue();

                                if (values.contains(baseReference+"."+methodName)) 
                                {
                                    base_key = key;
                                }  
                            }

                            //findout in the heap whre this object point to

                            Set<String> keySet = new HashSet<String>();

                            keySet.add(base_key.toString());
                            keySet.add(fieldName);

                            if(Heap.containsKey(keySet))
                            {
                                for (Integer element : Heap.get(keySet)) {
                                    
                                    Set<String> old_values = new HashSet<String>();
                                    
                                    if(graph.containsKey(element)) 
                                    {
                                        old_values=graph.get(element); 
                                    }  
                                    else
                                    {
                                        GC_line_no.put(element,-1);
                                    }
                                    old_values.add(lhs.toString()+"."+methodName);

                                    graph.put(element, old_values);
                                }
                            }
                            //if not found in the heap then point to the NULL pointer
                            else
                            {
                                if(graph.containsKey(0))
                                {
                                    Set<String> v = new HashSet<String>();
                                    v= graph.get(0);
                                    v.add(rightOp.toString()+"."+methodName);

                                    graph.put(0 , v);
                                }
                                else
                                {
                                    Set<String> v = new HashSet<String>();
                                    v.add(rightOp.toString()+"."+methodName);
                                    graph.put(0 , v);
                                }
                            }
                            

                        }
                    
                    }

                    else if (rightOp instanceof InvokeExpr)
                    {
                        InvokeExpr invokeExpr = (InvokeExpr) rightOp;

                        SootMethod invokedMethod = invokeExpr.getMethod();


                        for( Value arg : invokeExpr.getArgs())
                        {
                            for(Map.Entry<Integer, Set<String>> entry : graph.entrySet())
                            {
                                Integer key = entry.getKey();
                                Set<String> values = entry.getValue();

                                String reg = arg.toString()+"."+methodName;
                                
                                if(values.contains(reg))
                                {
                                    // System.out.println(key);
                                    queue.add(key);
                                }
                            }
                        }

                        parentMethod.put(invokedMethod.getName(),methodName);
                        returnstmt_parMap.put(methodName,lhs.toString());
                        processCFG(invokedMethod);

                         // Assign the return to the corresponding graph object
                        if(queueR.size()!=0)
                        {
                            Integer obj_line = queueR.poll();
                            Set<String> valueSet = new HashSet<>();
                            valueSet=graph.get(obj_line);
                            valueSet.add(lhs.toString()+"."+methodName);
                            graph.put(obj_line,valueSet);
                        } 

                    }

                }

            }

            //handle this and paramter refrennces
            else if(u instanceof JIdentityStmt)
            {
                
                JIdentityStmt identityStmt = (JIdentityStmt) u;
                Value lhs = identityStmt.getLeftOp();
                Value rhs = identityStmt.getRightOp();

                // System.out.println(queue);
                //handle parameter reference case
                if(rhs instanceof ParameterRef && !methodName.equals("main") && queue.size()!=0)
                {
                        // System.out.println("Unit: " + u );
                       Set<String> valueSet = new HashSet<>();

                       Integer obj_line = queue.poll();
                       valueSet=graph.get(obj_line);

                       String rg = lhs.toString()+"."+methodName;
                       valueSet.add(rg);

                       graph.put(obj_line,valueSet);
                }
                Set<String> parameterSet = new HashSet<>();

                if(parameter.containsKey(methodName))
                {
                    parameterSet=parameter.get(methodName);
                    parameterSet.add(lhs.toString());
                    parameter.put(methodName, parameterSet);

                }
                else
                {
                    parameterSet.add(lhs.toString());
                    parameter.put(methodName, parameterSet);
                }
                // System.out.println("New Paramter list : ");
                // System.out.println(parameter);

            }

            //handle the Invok statements
            else if(u instanceof InvokeStmt)
            {
                InvokeStmt invokeStmt = (InvokeStmt) u;
                String invokedMethod = invokeStmt.getInvokeExpr().getMethod().getName();

                // put the object in the queue so next function can access that parameter
                InvokeExpr invokeExpr = invokeStmt.getInvokeExpr();
                if (invokeExpr instanceof StaticInvokeExpr)
                {
                    for( Value arg : invokeExpr.getArgs())
                    {
                        for(Map.Entry<Integer, Set<String>> entry : graph.entrySet())
                        {
                            Integer key = entry.getKey();
                            Set<String> values = entry.getValue();

                            String reg = arg.toString()+"."+methodName;
                            
                            if(values.contains(reg))
                            {
                                // System.out.println(key);
                                queue.add(key);
                            }
                        }
                    }

                    parentMethod.put(invokedMethod,methodName);
                    //for handling the case where method which call and return something but program doesnot store
                    returnstmt_parMap.put(methodName,"s1");
                    processCFG(invokeStmt.getInvokeExpr().getMethod());
                }
            }

            //handle the return statements
            else if(u instanceof JReturnStmt)
            {  
                JReturnStmt stmt = (JReturnStmt) u;
                Value rhs = stmt.getOp();

                for(Map.Entry<Integer, Set<String>> entry : graph.entrySet())
                {
                    Integer key = entry.getKey();
                    Set<String> values = entry.getValue();

                    String reg = rhs.toString()+"."+methodName;
                    
                    if(values.contains(reg))
                    {
                        // System.out.println(key);
                        queueR.add(key);
                    }
                }
                

            }


            // logic of the GC collected variables

            // List<Local> before = liveLocals.getLiveLocalsBefore(u);
            // List<Local> after = liveLocals.getLiveLocalsAfter(u);

            // Convert lists to sets
            Set<Local> bfrset = new HashSet<>(before);
            Set<String> beforeSet = new HashSet<>();
            for (Local local : bfrset) 
            {
                beforeSet.add(local.toString());
            }

            Set<Local> afrset = new HashSet<>(after);
            Set<String> afterSet = new HashSet<>();
            for (Local local : afrset) 
            {
                afterSet.add(local.toString());
            }
            Set<String> result = beforeSet;
            // Perform set subtraction: remove elements in afterSet from beforeSet
            result.removeAll(afterSet);
            
            // System.out.println("result : " + result);
            
            //identify the result whether parameter refrence changed or not
            if(u instanceof JAssignStmt  && parameter.containsKey(methodName))
            {
                // System.out.println("without updated parameters: ");
                // System.out.println(parameter);
                JAssignStmt assignStmt = (JAssignStmt) u;
                Value lhs = assignStmt.getLeftOp();
                Value rhs = assignStmt.getRightOp();

                //if changed then update the parameter map
                if(!(lhs instanceof InstanceFieldRef) && ((rhs instanceof InstanceFieldRef)))
                {
                    Set<String> registers = parameter.get(methodName);
                    registers.add(lhs.toString());
                    registers.remove(rhs.toString());

                    parameter.put(methodName, registers);    
                }
                // System.out.println("updated parameters: ");
                // System.out.println(parameter);
            }

            int obj_line = u.getJavaSourceStartLineNumber();

            // System.out.println();
            
            // System.out.println("Graph After Sentence : " );

            // for (Map.Entry<Integer, Set<String>> entry : graph.entrySet()) 
            // {
            //     Integer key = entry.getKey();
            //     Set<String> value = entry.getValue();
            //     System.out.println("Key: " + key + ", Value: " + value);
            // }

            if(!(u instanceof ReturnStmt) )
            {

                for(String s : result)
                {
                    //remove the element from the graph which are the gced
                    for(Map.Entry<Integer, Set<String>> entry : graph.entrySet())
                    {
                        Integer key = entry.getKey();
                        Set<String> val = entry.getValue();
                        Set<String> values = Collections.newSetFromMap(new ConcurrentHashMap<>());
                        values.addAll(val);


                        String reg = s+"."+methodName;
                        // System.out.println(reg);
                        
                        if(values.contains(reg))
                        {
                            // remove the GC collected list in the graph
                            
                            //using heap check that parent and the child both are available


                            values.remove(reg);
                            graph.put(key,values);
                            // System.out.println(values);

                            if(values.isEmpty())
                            {                        
                                GC_line_no.put(key, obj_line);
                                Set<Integer> GC_collections = new HashSet<>();

                                if(method_GC.containsKey(methodName))
                                {
                                    GC_collections = method_GC.get(methodName);

                                    GC_collections.add(key);
                                    method_GC.put(methodName, GC_collections);
                                }
                                else
                                {
                                    GC_collections.add(key);
                                    method_GC.put(methodName, GC_collections);
                                }


                                //remove the entry from the graph
                                graph.remove(key);

                                // for (Map.Entry<Set<String>, Set<Integer>> en : Heap.entrySet())
                                // {
                                //     Set<String> heap_keys = en.getKey();
                                    
                                //     if(heap_keys.contains(key.toString()))
                                //     {
                                //         Heap.remove(heap_keys);
                                //     }
                                // }
                            
                            }
                        }

                        //check if any referncefield is also part of the object then also remove
                        for (String value : values) 
                        {
                            // System.out.println(values);
                            // if (value.startsWith(s) && value.endsWith(methodName)) 
                            String[] v = value.split("\\.");
                            // System.out.println( "0 : "+ v[0] + "Value : "+value);
                            if (v[0].equals(s) && value.endsWith(methodName))
                            {
                                // System.out.println("Equals to : "+ s);
                                // System.out.println("Hello");
                                values.remove(value);
                                graph.put(key,values);

                                if(values.isEmpty())
                                {                        
                                    GC_line_no.put(key, obj_line);
                                    Set<Integer> GC_collections = new HashSet<>();

                                    if(method_GC.containsKey(methodName))
                                    {
                                        GC_collections = method_GC.get(methodName);

                                        GC_collections.add(key);
                                        method_GC.put(methodName, GC_collections);
                                    }
                                    else
                                    {
                                        GC_collections.add(key);
                                        method_GC.put(methodName, GC_collections);
                                    }

                                    graph.remove(key);

                                    // for (Map.Entry<Set<String>, Set<Integer>> en : Heap.entrySet())
                                    // {
                                    //     // Map.Entry<Set<String>, Set<Integer>> en = heapIterator.next();
                                    //     Set<String> heap_keys = en.getKey();
                                        
                                    //     if(heap_keys.contains(key.toString()))
                                    //     {
                                    //         Heap.remove(heap_keys);
                                    //     }
                                    // }
                                    
                                }
                            } 
                        }
                    }
                }
                
                if( u instanceof JAssignStmt)
                {
                    JAssignStmt assignStmt = (JAssignStmt) u;
                    Value lhs = assignStmt.getLeftOp();

                    if( !(lhs instanceof JInstanceFieldRef) && (!(beforeSet.contains(lhs.toString()))) && (!(afterSet.contains(lhs.toString()))))
                    {
                        for(Map.Entry<Integer, Set<String>> entry : graph.entrySet())
                        {
                            Integer key = entry.getKey();
                            Set<String> values = entry.getValue();

                            String reg = lhs.toString()+"."+methodName;
                            
                            if(values.contains(reg))
                            {
                                values.remove(reg);
                                // System.out.println(values);
                                graph.put(key,values);

                                if(values.isEmpty())
                                {                        
                                    GC_line_no.put(key, obj_line);
                                    Set<Integer> GC_collections = new HashSet<>();

                                    if(method_GC.containsKey(methodName))
                                    {
                                        GC_collections = method_GC.get(methodName);

                                        GC_collections.add(key);
                                        method_GC.put(methodName, GC_collections);
                                    }
                                    else
                                    {
                                        GC_collections.add(key);
                                        method_GC.put(methodName, GC_collections);
                                    }


                                    //remove the entry from the graph
                                    graph.remove(key);

                                    // for (Map.Entry<Set<String>, Set<Integer>> en : Heap.entrySet())
                                    // {
                                    //     Set<String> heap_keys = en.getKey();
                                        
                                    //     if(heap_keys.contains(key.toString()))
                                    //     {
                                    //         Heap.remove(heap_keys);
                                    //     }
                                    // }
                                
                                }
                            }
                            for (String value : values) 
                            {
                                // System.out.println(values);
                                // if (value.startsWith(lhs.toString()) && value.endsWith(methodName)) 
                                String[] v = value.split("\\.");
                        
                                if (v[0].equals(lhs.toString()) && value.endsWith(methodName))
                                {
                                    // System.out.println("Hello");
                                    values.remove(value);
                                    graph.put(key,values);

                                    if(values.isEmpty())
                                    {                        
                                        GC_line_no.put(key, obj_line);
                                        Set<Integer> GC_collections = new HashSet<>();

                                        if(method_GC.containsKey(methodName))
                                        {
                                            GC_collections = method_GC.get(methodName);

                                            GC_collections.add(key);
                                            method_GC.put(methodName, GC_collections);
                                        }
                                        else
                                        {
                                            GC_collections.add(key);
                                            method_GC.put(methodName, GC_collections);
                                        }

                                        graph.remove(key);

                                        // for (Map.Entry<Set<String>, Set<Integer>> en : Heap.entrySet())
                                        // {
                                        //     // Map.Entry<Set<String>, Set<Integer>> en = heapIterator.next();
                                        //     Set<String> heap_keys = en.getKey();
                                            
                                        //     if(heap_keys.contains(key.toString()))
                                        //     {
                                        //         Heap.remove(heap_keys);
                                        //     }
                                        // }
                                        
                                    }
                                } 
                            }

                        }
                    }
                }
            }

            if((u instanceof JIdentityStmt ) )
            {
                JIdentityStmt identityStmt = (JIdentityStmt) u;
                Value lhs = identityStmt.getLeftOp();
                
                if( (!(lhs instanceof InstanceFieldRef)))
                {

                    if((!(beforeSet.contains(lhs.toString()))) && (!(afterSet.contains(lhs.toString()))))
                    {
                        for(Map.Entry<Integer, Set<String>> entry : graph.entrySet())
                        {
                            Integer key = entry.getKey();
                            Set<String> values = entry.getValue();

                            String reg = lhs.toString()+"."+methodName;
                            
                            if(values.contains(reg))
                            {
                                values.remove(reg);
                                // System.out.println(values);
                                graph.put(key,values);

                                if(values.isEmpty())
                                {                        
                                    GC_line_no.put(key, obj_line);
                                    Set<Integer> GC_collections = new HashSet<>();

                                    if(method_GC.containsKey(methodName))
                                    {
                                        GC_collections = method_GC.get(methodName);

                                        GC_collections.add(key);
                                        method_GC.put(methodName, GC_collections);
                                    }
                                    else
                                    {
                                        GC_collections.add(key);
                                        method_GC.put(methodName, GC_collections);
                                    }


                                    //remove the entry from the graph
                                    graph.remove(key);

                                    // for (Map.Entry<Set<String>, Set<Integer>> en : Heap.entrySet())
                                    // {
                                    //     Set<String> heap_keys = en.getKey();
                                        
                                    //     if(heap_keys.contains(key.toString()))
                                    //     {
                                    //         Heap.remove(heap_keys);
                                    //     }
                                    // }
                                
                                }
                            }
                        }
                    }   
                }
            }

            if(u instanceof JInvokeStmt)
            {
                String register_value= "s1";
                
                for(Map.Entry<Integer, Set<String>> entry : graph.entrySet())
                {
                    Integer key = entry.getKey();
                    Set<String> values = entry.getValue();

                    String reg = register_value+"."+methodName;
                    
                    if(values.contains(reg))
                    {
                        values.remove(reg);
                        // System.out.println(values);
                        graph.put(key,values);

                        if(values.isEmpty())
                        {                        
                            GC_line_no.put(key, obj_line);
                            Set<Integer> GC_collections = new HashSet<>();

                            if(method_GC.containsKey(methodName))
                            {
                                GC_collections = method_GC.get(methodName);

                                GC_collections.add(key);
                                method_GC.put(methodName, GC_collections);
                            }
                            else
                            {
                                GC_collections.add(key);
                                method_GC.put(methodName, GC_collections);
                            }


                            //remove the entry from the graph
                            graph.remove(key);

                            // for (Map.Entry<Set<String>, Set<Integer>> en : Heap.entrySet())
                            // {
                            //     Set<String> heap_keys = en.getKey();
                                
                            //     if(heap_keys.contains(key.toString()))
                            //     {
                            //         Heap.remove(heap_keys);
                            //     }
                            // }
                        
                        }
                    }
                    for (String value : values) 
                    {
                        // System.out.println(values);
                        String[] v = value.split("\\.");
                        
                        if (v[0].equals(register_value) && value.endsWith(methodName)) 
                        {
                            // System.out.println("Hello");
                            values.remove(value);
                            graph.put(key,values);

                            if(values.isEmpty())
                            {                        
                                GC_line_no.put(key, obj_line);
                                Set<Integer> GC_collections = new HashSet<>();

                                if(method_GC.containsKey(methodName))
                                {
                                    GC_collections = method_GC.get(methodName);

                                    GC_collections.add(key);
                                    method_GC.put(methodName, GC_collections);
                                }
                                else
                                {
                                    GC_collections.add(key);
                                    method_GC.put(methodName, GC_collections);
                                }

                                graph.remove(key);

                                // for (Map.Entry<Set<String>, Set<Integer>> en : Heap.entrySet())
                                // {
                                //     // Map.Entry<Set<String>, Set<Integer>> en = heapIterator.next();
                                //     Set<String> heap_keys = en.getKey();
                                    
                                //     if(heap_keys.contains(key.toString()))
                                //     {
                                //         Heap.remove(heap_keys);
                                //     }
                                // }
                                
                            }
                        } 
                    }
                    

                }

            }

            
            if(u instanceof JReturnVoidStmt) 
            {
                if(methodName.equals("main"))
                {
                    
                    Set<Integer> GC_method = new HashSet<>();
                    GC_method = method_GC.get("main");

                    for (Map.Entry<Integer, Integer> entry : GC_line_no.entrySet())
                    {

                        Integer key = entry.getKey();
                        Integer value = entry.getValue();
                        // System.out.println("Key: " + key + ", Value: " + value);
                        if(value == -1 && key!=0)
                        {
                            value = obj_line;
                            GC_method.add(key);
                            GC_line_no.put(key, value);
                        }
                    }
                    
                    method_GC.put("main", GC_method);
                }
            }
            else
            {
                if(u instanceof JReturnStmt)
                {
                    JReturnStmt returnStmt = (JReturnStmt) u;
                    Value returnValue = returnStmt.getOp();
                    String Parent_methodName = parentMethod.get(methodName);

                    // System.out.println("Parent Method : " );
                    // System.out.println(parentMethod);

                    //first add the element in the map refer to the parent 
                    if(returnstmt_parMap.containsKey(Parent_methodName))
                    {
                        String Parent_register = returnstmt_parMap.get(Parent_methodName);

                        String reg = returnValue.toString()+"."+methodName;
                        String Parent_entry = Parent_register+"."+Parent_methodName;

                        for(Map.Entry<Integer, Set<String>> entry : graph.entrySet())
                        {
                            Integer key = entry.getKey();
                            Set<String> values = entry.getValue();

                            if(values.contains(reg))
                            {
                                values.add(Parent_entry);
                                values.remove(reg);
                                graph.put(key,values);
                            }

                            for(String value : values)
                            {
                                if(value.startsWith(returnValue.toString()) && value.endsWith(methodName))
                                {
                                    String[] parts = value.split("\\.");
                                    String parent_refernce_entry = Parent_register +"."+parts[1]+"."+Parent_methodName;

                                    values.add(parent_refernce_entry);
                                    values.remove(value);

                                    graph.put(key,values);
                                    
                                }
                            }

                        }
                    }
                    
                }
            }
            // System.out.println("\n");
            // System.out.println("Graph After Optimization: " );

            // for (Map.Entry<Integer, Set<String>> entry : graph.entrySet()) {
            //     Integer key = entry.getKey();
            //     Set<String> value = entry.getValue();
            //     System.out.println("Key: " + key + ", Value: " + value);
            // }
            
            // System.out.println("\n");
            // System.out.println("Heap : " );
            // for (Map.Entry<Set<String>, Set<Integer>> entry : Heap.entrySet()) 
            // {
            //     Set<String> key = entry.getKey();
            //     Set<Integer> value = entry.getValue();
            //     System.out.println("Key: " + key + ", Value: " + value);
            // }

            // // Printing GC_line_no
            // System.out.println("\n");
            // System.out.println("GC_line_no:");
            // for (Map.Entry<Integer, Integer> entry : GC_line_no.entrySet()) {
            //     System.out.println("Key: " + entry.getKey() + ", Value: " + entry.getValue());
            // }
            
            // System.out.println("\n");
            // // Printing method_GC
            // System.out.println("\nmethod_GC:");
            // for (Map.Entry<String, Set<Integer>> entry : method_GC.entrySet()) {
            //     System.out.println("Key: " + entry.getKey() + ", Value: " + entry.getValue());
            // }
            
            // System.out.println("\n\n");

            // System.out.println("\n---------------------------\n");

        }
        // System.out.println("\n---------------------------\n");
        
    }

}
