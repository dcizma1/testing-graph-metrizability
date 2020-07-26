import networkx as nx
import numpy as np
from itertools import combinations
import cvxopt
from cvxopt import glpk,solvers
import time
from decimal import Decimal, ROUND_HALF_UP
from fractions import Fraction

#Given a graph G and prevPaths a list of all paths of a certain length l returns all paths of length l + 1
#Note that this function double counts paths
def findPaths(G, prevPaths = []):
    if not prevPaths:
        return [list(e) for e in G.edges] + [list(e)[::-1] for e in G.edges]
    else:
        return [[u] + p for p in prevPaths for u in G.neighbors(p[0]) if u not in p ]




#Check if weights induce a path system
def checkMetricCompatibility(G, system, weights, strict = False):
    N = len(G.nodes)

    #This defines edge weight function
    def wghtFxn(i,j,dictEdge):
        edge = (i,j) if i < j else (j,i)
        return weights[edge]
    #Given a path gives its weight
    def pathWeight(p):
        sum = 0
        for i in range(0,len(p) - 1):
            sum = sum + wghtFxn(p[i],p[i+1], [])
        return sum

    #Get all the shortest distances between vtxs
    len_path = dict(nx.all_pairs_dijkstra_path_length(G,weight=wghtFxn))

    #We check is all the paths in the system are geodesics wrt to weightStrings
    for i in range(1, N):

        for j in range(0, i):

            #shortest distance between ij wrt weights
            ijDist = len_path[i][j]
            #weight of ij path in the path system
            pthSysDist = pathWeight(system[i][j])

            #If the actual disance is smaller than that of ij path from the system return false
            if ijDist < pthSysDist:
                return False

    #In the strict case we need to also check each path is unique
    if strict:
        for  i in range (1,N):
            #pred is a dictionary which contains all the predeccesors of all paths with source i
            pred, _ = nx.dijkstra_predecessor_and_distance(G, i, weight = wghtFxn)
            for j in range(0,i):
                #If j has two predeccesors on the shortest ij path then it is not unique

                if len(pred[j]) > 1:
                    return False

    return True


#Sets up and solves a linear program to check our System
#We use CVXOPT to solve the lp
def findSolutionOfSystem(constraints, edges, strict = False):
    M = len(edges)
    K = len(constraints)
    c = cvxopt.matrix(np.zeros(M), tc='d')
    if not strict:
        h = np.zeros(K + M)
    else:
        h = np.full(K+M,-1.)
    G = constraints
    for i in range(0,M):
        h[K+i] = -1
        newrow = np.zeros(M)
        newrow[i] = -1
        G.append(newrow.tolist())
    h = cvxopt.matrix(h,tc='d')
    G = cvxopt.matrix(G,tc='d')
    G = G.trans()

    weights = {}
    status = 0
    solvers.options['show_progress'] = False
    solvers.options['glpk'] = {'msg_lev' : 'GLP_MSG_OFF'}


    sol = cvxopt.solvers.lp(c, G, h, I=set(range(0,M)), solver = 'glpk',options={'glpk':{'msg_lev':'GLP_MSG_OFF'}})
    if sol['status'] == 'optimal':
        status = 1

        #Converting Solution to integer Solution
        numerators = []
        denominators = []
        for i in range(0,M):
            w = Fraction(sol['x'][i]).limit_denominator()
            numerators.append(w.numerator)
            denominators.append(w.denominator)
        numerators = np.array(numerators)
        LCM = np.lcm.reduce(denominators)

        for i in range(0,M):
            weights[edges[i]] = int(numerators[i] * LCM / denominators[i])
    elif sol['status'] == 'primal infeasible':
        status = -1
    else:
        status = 0

    return [weights, status]


#The input nonIndPaths is a list of paths
#This function unindexed paths and indexes them in the following sense:
#It create a dictionary whose keys are vertex pairs (u,v).
#The value at the (u,v) index is a list of all the uv paths in nonIndPaths
def indexPaths(nonIndPaths):
    indPaths = {}
    for p in nonIndPaths:
        if p[0] > p[-1]:
            key = (p[0], p[-1])
            if  key in indPaths:
                indPaths[key].append(p)
            else:
                indPaths[key] = []
                indPaths[key].append(p)
    return indPaths

#This function inputs a graph G, a path system and a dictionary of paths indexed by a tuple of their endpoints
#The output is a list of list where each sublist has length |E| where E is the set of edges in G and contains, -1,0,1 in each index
#These sublists correspond to a systems inequalities Ax<= b some weight function inducing this system must satisfy

def getNewConstraints(G,system, indPaths):
    newConstraints = []
    vtxs = list(G.nodes)
    edges = list(G.edges)
    #dictionary which maps an edge to its index

    N = len(vtxs)
    numEdge = len(edges)
    edgeToIndex = {}
    for i, e in enumerate(edges):
        edgeToIndex[e] = i

    for i in range(0, N):
        for j in range(0,i):
            key = (i,j)
            if key in indPaths:
                #our desgnated geodesic
                geo = system[i][j]
                for p in indPaths[key]:
                    constr = np.zeros(numEdge, dtype=int)
                    #For each edge in the geodesic we add 1
                    for k in range(0,len(geo) - 1):
                        e = (geo[k], geo[k+1]) if geo[k] < geo[k+1] else (geo[k+1], geo[k])
                        edgeInd = edgeToIndex[e]
                        constr[edgeInd] = constr[edgeInd] + 1
                    #For each edge in the other path we add -1
                    for k in range(0,len(p) - 1):
                        e = (p[k], p[k+1]) if p[k] < p[k+1] else (p[k+1], p[k])
                        edgeInd = edgeToIndex[e]
                        constr[edgeInd] = constr[edgeInd] - 1
                    #check is constaint is not trivial
                    if constr.any():
                        constr=constr.tolist()
                        newConstraints.append(constr)
    return newConstraints

#This function inputs a graph G, a path system and a non-indexed list of all paths of length l > 0 in G
#It outputs new constraints the path system must satisfy and all paths of length l+1 in G
def getNewPathsAndConstraints(G, system, oldNonIndPaths):
    newNonIndPaths = findPaths(G, oldNonIndPaths)
    newIndPaths = indexPaths(newNonIndPaths)
    newConstraints = getNewConstraints(G, system, newIndPaths)
    return [newNonIndPaths, newConstraints]


#Check if Path System in graph G is metrizable
def checkIfMet(G,System, strict = False):
    PRINT = False
    N = len(G.nodes)
    Edges = list(G.edges)
    #In order to account for the trivial case of trees we first check if constant weights induce our systems
    constWeights = dict.fromkeys(Edges, 1)

    #this is a list which will contain all the constraints of our linear program
    #Here they are stored as lists of -1,0,1 of size |Edges|
    constraints = []

    #list where i th index contains all paths in G of length i + 1
    paths = []

    #Initialize paths and constraints.
    # Note at this point only edges are in paths and similarly the constraints are trivial
    newPaths,  constraints = getNewPathsAndConstraints(G, System, [])
    paths.append(newPaths)
    #We loop until we get a non-empty list of  constraints
    while not constraints:
        newPaths,  newConstraints = getNewPathsAndConstraints(G, System, paths[-1])

        paths.append(newPaths)
        constraints = constraints + newConstraints


    possibleWeights, exitCode = findSolutionOfSystem(constraints, Edges, strict)

    count = 0

    while True:
        if PRINT:
            print(count)
        #System is infeasible, i.e. not metrizable
        if exitCode == -1:

            if PRINT:
                print("System is Infeasible")
            return False

        #System may be feasible, we first need to check is the weights induce the system
        elif exitCode == 1:
            goodWeights = checkMetricCompatibility(G,  System,  possibleWeights, strict)

            if goodWeights:
                if PRINT:
                    print("System is consistent with following weights:")
                    print(weights)
                #print(metricCheckTime/(time.time()-totalTime1)*100)
                return True
            else:
                newPaths,  newConstraints = getNewPathsAndConstraints(G, System, paths[-1])
                paths.append(newPaths)
                constraints = constraints + newConstraints

                possibleWeights, exitCode = findSolutionOfSystem(constraints, Edges, strict)

                #Sanity check
                if count > N:
                    print("Somethings is Wrong")
                    return False

        #In the scenario where the linear program can't be solved for some reason
        else:
            print("No Good")
            print("Exit Code " + str(exitCode))
            return False
        count = count + 1


#Obtain the graph of a path system, i.e. it is the graph containing every edge in the system
def getGraphFromSystem(system):
    G = nx.Graph()
    N = len(system)
    G.add_nodes_from(list(range(0,N)))
    for i in range(0,N):
        for j in range(0,i):
            if len(system[i][j]) == 2:
                G.add_edge(i,j)

    return G

#Call this function to check if system is metrizable
def checkIfSystemIsMet(system,strict = False):
    G = getGraphFromSystem(system)
    return checkIfMet(G,system, strict)
