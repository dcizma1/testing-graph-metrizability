import numpy as np
import copy
import networkx as nx
from CheckSystem import *
import time
from collections import deque


#To find all the neighborly path systems of a given graph we do the following:
#1. For every vertex v in G we generate all of the spanning trees of G
#   rooted at v containing the edges incident to v
#2. We then check which collections of trees are consistent

#We define a tree as a collection of paths rooted at a node
class Tree():
    def __init__(self,root):
        #root of the tree
        self.root = root
        #paths of the tree starting at the root
        self.paths = {}
        self.paths[root] = [root]
        #vertices in the tree
        self.vertices = [root]
        #dictionary of vertex predeccesors
        self.pred = {}
        self.pred[root] = -1
        #dictionary whose keys are 2-tuple of edge
        #Contains all the subpaths which are linearly by the tree ordering
        self.subPaths = {}


    #Adding an edge to a tree
    #The input must include a vertex already in the tree and one vertex not in the tree
    def addEdge(self,u,v):
        U = u
        V = v
        if u in self.vertices and v not in self.vertices:
            U = u
            V = v
        elif v in self.vertices and u not in self.vertices:
            U = v
            V = u
        else:
            print("Not a valid edge")
            return
        #This is the path from the root to the new vertex
        path = self.paths[U].copy()
        path.append(V)
        self.paths[V] = path

        self.vertices.append(V)

        self.pred[V] = U

        self.subPaths[V] = {}
        for i in range(0, len(path) - 1):
            self.subPaths[(path[i],V)] = path[i:]
            if i != 0:
                self.subPaths[(V, path[i])] = path[-1:i-1:-1]
            else:
                self.subPaths[(V, path[i])] = path[-1::-1]


    def getSubPaths(self):
        return self.subPaths

    def getPaths(self):
        return self.paths

    def getVertices(self):
        return self.vertices



#Find all spanning trees of G which contain TBase
#Here TBase a rooted subtree of G
#The algorithm used here is similar to the one outline in the paper:
#FINDING ALL SPANNING TREES OF DIRECTED AND UNDIRECTED GRAPHS, Authors: Gabow and Myers
#But the connectivity test outlined is different and a stack is used instead of recursion
def generateSpanningTrees(G, TBase = None):

    N = len(G.nodes)
    TREES = []
    #Stores edge used in previous iterations
    UsedEdges = set()
    #Keeps a dictionary whose keys are sets of edges to see if they disconnect a graph
    connDict = {}
    if TBase is not None:
        T0 = TBase
    else:
        T0 = Tree(0)

    if len(T0.getVertices()) == N:
        return [T0]

    #TreesToExtend = [[T0,EdgesNotAllowed]]
    TreesToExtend = deque()
    TreesToExtend.append([T0,UsedEdges])
    while TreesToExtend:

        [currT, currUsedEdges] = TreesToExtend.pop()

        connected = True
        #while Graph - currUsedEdges is connected
        while connected:
            edge,  extendedTree = extendTree(G, currT, currUsedEdges)

            extTree = extendedTree[0]
            #If the new tree has N vertices then it is spanning
            if len(extTree.getVertices()) == N:
                TREES.append(extTree)
            else:
                TreesToExtend.append(extendedTree)

            currUsedEdges.add(edge)
            frozCurrUsedEdges = frozenset(currUsedEdges)
            #Check currUsedEdges is in the connectivity dictionary
            #If not check if G - currUsedEdges is connected and at it to dictionary
            if frozCurrUsedEdges not in connDict:
                connDict[frozCurrUsedEdges] = checkConnectivity(G,currUsedEdges)
            connected = connDict[frozCurrUsedEdges]


    return TREES



#Submethod to extends tree by adding
#Notallowed is a set of edges previously used by other trees in the stack
def extendTree(G, T, UsedEdges):
    verticesUsed = T.getVertices()
    for u in verticesUsed:
        for w in G.neighbors(u):
            if w not in verticesUsed:
                edge = (u,w) if u < w else (w,u)
                if edge not in UsedEdges:
                    TNew = copy.deepcopy(T)
                    newUsedEdges = copy.deepcopy(UsedEdges)
                    TNew.addEdge(u,w)
                    return [edge, [TNew, newUsedEdges]]


def checkConnectivity(G,edges):
    H = copy.deepcopy(G)
    H.remove_edges_from(edges)
    return nx.is_connected(H)


#check if two trees are consistent
#i.e. we check if there is an induced uv subpath is both T1 and T2 then they must agree
def checkTreesCompatible(T1,T2):
    subPaths1 = T1.getSubPaths()
    subPaths2 = T2.getSubPaths()
    for pair in subPaths1.keys() & subPaths2.keys():
        if subPaths1[pair] != subPaths2[pair]:
            return False

    return True

#In this scenario a system is a collection of tree, where for each v in G there is a tree rooted at v
#Moreover, these tree must be pairwise compatible

#To find all the the tree systems of the graph we view the collection of rooted trees of G as an N-partite Graph
#where N is the number of vtxs of G. The partition set corresponding to the vtx v is the set of trees rooted at v
#There is an edge between two trees if they are compatible
#A tree system in this graph is an N-clique

#The arguments are a graph G and a boolean IncludeEdges. If IncludeEdges edge is true then every tree rooted at a vtx v must contain
#all the neighbors of v
def generatePathSystems(G, IncludeEdges = True):
    N = len(G.nodes)
    #Lists where each index specifices a vertex
    #This incluces all spanning trees rooted at that vertex
    #From the graph point of view, the index i contains the i th partition set of our N-partite graph
    SpanningTrees = []
    #For each vertex v there is a dictionary whose keys are the tree rooted at v
    #Given a rooted tree T at v the value at the index T is a list of size N
    #In the u th index of the list is a set of trees rooted at u which are compatible with T
    Compatibility = []

    #For each vertex v, gives the the total number of trees which are compatible to some tree rooted at v
    #Note that if there is a tree T which is compatible to two different trees which are both rooted at v then T is counted twice
    CompatibilityCount = []

    #Initialize dictionary and counts
    for i in range(0,N):
        Compatibility.append({})
        CompatibilityCount.append(0)


    for v in range(0,N):
        TBase = Tree(v)
        #If we includ
        if IncludeEdges:
            for u in G.neighbors(v):
                TBase.addEdge(u,v)

        SpanningTrees.append([])
        SpanningTrees[-1]= generateSpanningTrees(G,TBase)

    #We loop through the trees to find all pairwise compatible trees
    for i in range(0,N):
        for indT, T in enumerate(SpanningTrees[i]):
            #We first check the indT is not an index in the dictionary
            #since it may have been defined in a previous iteration
            if indT not in Compatibility[i]:
                #The value at indT is a list of size N
                #A the j != i index is a set of tree indices of trees roote at j compatible with T
                Compatibility[i][indT] = []
                for l in range(0,N):
                    Compatibility[i][indT].append(set())
            #We now loop through the remaining trees to find any trees compatible with T
            for j in range(i+1,N):
                for indS, S  in enumerate(SpanningTrees[j]):
                    if indS not in Compatibility[j]:
                        Compatibility[j][indS] = []
                        for l in range(0,N):
                            Compatibility[j][indS].append(set())
                    #If the two trees are compatible we update the compatibility dictionaries and the compatibility counts
                    if checkTreesCompatible(T,S):
                        Compatibility[i][indT][j].add(indS)
                        Compatibility[j][indS][i].add(indT)

                        CompatibilityCount[i] = CompatibilityCount[i] + 1
                        CompatibilityCount[j] = CompatibilityCount[j] + 1

            #We check if there exists a vtx j such that there are no j rooted trees compaible with out current tree.
            #If such a vertex j exists we set Compatibility[i][keyT][i]  to be False otherwise it is True
            goodTree = True
            for l in range(0,N):
                if i == l:
                    continue
                if len(Compatibility[i][indT][l]) == 0:
                    goodTree = False

            Compatibility[i][indT][i] = goodTree

    #In finding tree systems we start with the vertex which has the smallest compatibility count
    minIndex = np.argmin(CompatibilityCount)
    #List to store full tree systems
    #These systems are stored as dictionary.
    #Here, the keys are vertices and the values the index of the tree rooted at that vertex
    SystemList = []
    count = 0
    for indT in range(0,len(SpanningTrees[minIndex])):
        #This is a list a partial systems
        #The partial systems are also stored as dictionaries
        PartialSystemList = []
        #If Compatibility[minIndex][indT][minIndex] is false then this tree can't be extended to a full system
        if Compatibility[minIndex][indT][minIndex]:
            PartialSystemList = [{}]
            PartialSystemList[-1][minIndex] = indT
        #While the list of partial systems is not empty attempt to extends these systems to full systems
        while PartialSystemList:
            sys = PartialSystemList.pop()
            completingSystem(sys, N, Compatibility, PartialSystemList, SystemList)

    return [SystemList, SpanningTrees]


#Given a partial system this function attempts to complete ir
#The arguments it take are: currSystem - current partial system, numVtxs - order of G, Compatibility - compatibility dictionary of the trees,
#PartialSystemList - a list of partial systems that need to be expanded, SystemList - a list a full path systems
def completingSystem(currSystem, numVtxs, Compatibility, PartialSystemList, SystemList):

    #these are the vertices which are currently defined in the partial system
    definedNodes = currSystem.keys()
    #List of vertices which are not defined in the current systsem
    undefinedNodes = list(set(range(0,numVtxs)) - definedNodes)

    definedNodes = list(currSystem.keys())

    vtx = -1
    compatibleTrees = []
    compatibleCount = np.inf
    for k in undefinedNodes:
        #For each undefined vertex v we find all the the tree rooted at v which are compatible with the partial system
        l = definedNodes[0]
        treeSets = [Compatibility[v][currSystem[v]][k] for v in definedNodes]
        compTrees = Compatibility[l][currSystem[l]][k].intersection(*treeSets)
        numCompTrees = len(compatibleTrees)

        #we keep track of which vertex has the least number of compatible trees
        if numCompTrees < compatibleCount:
            compatibleCount = numCompTrees
            compatibleTrees = list(compTrees)
            vtx = k

    #If there are is only one undefined vertex left, then this partial system uniquely extends to a full system
    if len(undefinedNodes) == 1:
        #sanity check
        if len(compatibleTrees) > 1:
            print("Something is Wrong - File:GeneratingSystems.py")
        #If the system is complete we add it to SystemList
        elif len(compatibleTrees) == 1:
            currSystem[vtx] = compatibleTrees[0]
            SystemList.append(currSystem)
    else:
        #If the system is still not complete we add all the new partial systems to PartialSystemList
        for indT in compatibleTrees:
            if  Compatibility[vtx][indT][vtx]:
                system = currSystem.copy()
                system[vtx] = indT
                PartialSystemList.append(system)

#The arguments: pathSys - This is a list of tree indices which make up a tree system, trees - a list which contains the trees rooted at each vtxs
#This function returns a collection of paths, represented as lists, which correspond ro to the path system
def convertPathSystem(pathSys, trees):
    N = len(pathSys)
    Sys = []
    for i in range(0,N):
        Sys.append([])
        for j in range(0, i):
            Sys[-1].append([])
            Sys[i][j] = trees[i][pathSys[i]].getPaths()[j]

    return Sys

#This path system representation is used when printing out path systems as lists
def convertToFullPathSystem(pathSys):

    N = len(pathSys)
    Sys = []
    for i in range(0,N):
        Sys.append([])

    for i in range(0,N):
        for path in pathSys[i]:
            Sys[path[0]].append(path)
            Sys[path[-1]].append(path[::-1])

    return Sys

#Check all systems of a graph whether or not they are metrizable
def checkSystems(G, IncludeEdges = True, strict = False):
    PRINT = False
    #Get all the path systems of G
    systems, trees = generatePathSystems(G, IncludeEdges)
    total = len(systems)
    #Count of non-metrizable systems
    nonMet = 0
    #Count of Metrizable systems
    Met = 0
    #Counts the number of systems currently checked
    count = 0
    systemType = "strictly " if strict else ""
    print("Number Of Systems: " + str(total))
    #Loop through all path systems to check metrizability
    for system in systems:

        sys = convertPathSystem(system, trees)

        if PRINT:
            print(convertToFullPathSystem(sys))

        isMetrizable = checkIfMet(G,sys, strict)
        if isMetrizable:
            Met = Met + 1
        else:
            nonMet = nonMet + 1
            print(sys)

            #print("Non-Additive Systems: " + str(nonMet))

        count = count + 1
        if count % 500 == 0:
            print("Systems checked: " + str(count) + "    Non-"+ systemType+ "metrizable Systems Found: " + str(nonMet))

    print("Total Systems: " + str(total) + "   "+systemType.title()+ "Metrizable Systems: " + str(Met) \
            + "   Non-"+ systemType.title() +"Metrizable Systems: " + str(nonMet))

    return [total, Met, nonMet]


if __name__ == "__main__":
    l = [1,2,3,4,5,6]
    G = nx.complete_graph(5)
    T = Tree(0)
    T.addEdge(0,1)
    #print(list(G.edges))
    print(checkSystems(G, False))
