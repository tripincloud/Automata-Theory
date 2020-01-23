# -*- coding: utf-8 -*-
from transition import *
from state import *
import os
import copy
from sp import *
from parser import *
import itertools
from automateBase import AutomateBase

#####
# Fonctions du projet (utilisées seulement en interne)
#####
    
def isFinal (l) :
    return any(s.fin for s in l)

def succElem(auto, state, lettre):
    """State x str -> list[State]
    rend la liste des états accessibles à partir d'un état
    state par l'étiquette lettre
    """
    successeurs = []
    # t: Transitions
    for t in auto.getListTransitionsFrom(state):
        if t.etiquette == lettre and t.stateDest not in successeurs:
            successeurs.append(t.stateDest)
    return successeurs


def succ (auto, listStates, lettre):
    """list[State] x str -> list[State]
    rend la liste des états accessibles à partir de la liste d'états
    listStates par l'étiquette lettre
    """
    succ = []
    for src in listStates:
        for s in succElem(auto, src, lettre):
            if s not in succ:
                succ.append(s)
    return succ    
    
def estComplet(auto,alphabet) :
    """ Automate x str -> bool
     rend True si auto est complet pour alphabet, False sinon
    """
    # On regarde pour chaque état la liste des étiquettes des transitions sortantes
    for s in auto.listStates:
        lettres = []
        for t in auto.getListTransitionsFrom(s):
            if t.etiquette not in lettres:
                lettres.append(t.etiquette)
        # S'il manque une lettre, auto n'est pas complet
        for l in alphabet:
            if l not in lettres:
                return False
    return True

def estDeterministe(auto) :
    """ Automate  -> bool
    rend True si auto est déterministe, False sinon
    """
    # 1 seul état initial autorisé
    if len(auto.getListInitialStates()) > 1:
        return False
    for s in auto.listStates:
        lettres = []
        for t in auto.getListTransitionsFrom(s):
            # On ne doit pas voir deux fois la même lettre sortant de l'état s
            if t.etiquette not in lettres:
                lettres.append(t.etiquette)
            else:
                return False
    return True

def freshId(self):
    # Rend max(identifiants de self)+1 pour s'assurer d'avoir un id frais
    listeId = []
    for s in self.listStates:
        listeId.append(s.id)
    return max(listeId)+1
    
def completeAutomate(auto,alphabet) :
    """ Automate x str -> Automate
    rend l'automate complété d'auto, par rapport à alphabet
    """
    comp = copy.deepcopy(auto)
    # S'il est déjà complet, on renvoie juste la copie
    if estComplet(auto,alphabet):
        return comp
    # Sinon on rajoute un puits ...
    puits = State(freshId(comp), False, False, "Puits")
    comp.addState(puits)
    # ... avec des self-loops ...
    for l in alphabet:
        comp.addTransition(Transition(puits, l, puits))
    # ... et avec les transitions manquantes pointant vers lui
    for s in auto.listStates:
        lettres = []
        for t in auto.getListTransitionsFrom(s):
            if t.etiquette not in lettres:
                lettres.append(t.etiquette)
        for l in alphabet:
            if l not in lettres:
                comp.addTransition(Transition(s, l, puits))
    return comp
    
def determinisation(auto) :
    """ Automate  -> Automate
    rend l'automate déterminisé d'auto
    """
    if estDeterministe(auto):
        return copy.deepcopy(auto)
    alphabet = auto.getAlphabetFromTransitions()
    currentStates = auto.getListInitialStates()
    # Unique état initial du déterminisé
    init = State(0, True, isFinal(currentStates), str([s.label for s in currentStates]))
    # workingList est une liste de tableaux à deux éléments [States du déterminisé, liste correspondante d'états de auto]
    # Contient uniquement init au départ
    workingList = [[init,currentStates]]
    # okList est la liste de ceux qu'on a déjà traités
    okList = []       
    # transList est la liste des transitions du déterminisé
    transList = []
    cpt = 1
    
    # Tant qu'il reste des états à traiter
    while len(workingList) > 0:
        # On récupère le premier élément de la liste et on le met dans okList
        currentS = workingList[0][0]
        currentStates = workingList[0][1]
        okList.append(workingList.pop(0))
        for l in alphabet:
            # On regarde les successeurs succStates
            succStates = succ(auto,currentStates,l)
            succS = State(0,False,False) #valeur bidon
            found = False
            for list in workingList + okList:
                # Cas où succStates est déjà connu
                if list[1] == succStates:
                    # On récupère juste l'état déjà créé
                    succS = list[0]
                    found = True
            # Cas où succ est nouveau
            if not found:
                # On crée l'état du déterminisé qui correspond et on l'ajoute à workingList
                succS = State(cpt, False, isFinal(succStates), str([s.label for s in succStates]))
                workingList.append([succS,succStates])
                cpt = cpt+1
            # Dans les deux cas, on ajoute la transition correspondante
            transList.append(Transition(currentS, l, succS))
    return AutomateBase(transList)
    
def complementaire(auto,alphabet):
    """ Automate -> Automate
    rend  l'automate acceptant pour langage le complémentaire du langage de a
    """
    # On déterminise et complète auto
    deter = determinisation(auto)
    comp = completeAutomate(deter,alphabet)
    # Et on inverse les états finaux et non finaux
    for s in comp.listStates:
        s.fin = not s.fin
    return comp

def intersection (auto0, auto1):
    """ Automate x Automate -> Automate
    rend l'automate acceptant pour langage l'intersection des langages des deux automates
    """
    alphabet = auto0.getAlphabetFromTransitions()
    cpt = 0
    # Même principe que pour determinisation
    workingList = []
    okList = []
    transList = []
    
    def final (s0,s1) :
        return (s0.fin and s1.fin)
    
    # Création des états initiaux de l'automate produit
    for s0 in auto0.getListInitialStates():
        for s1 in auto1.getListInitialStates():
            workingList.append([State(cpt, True, final(s0,s1), s0.label + s1.label),[s0,s1]])
            cpt = cpt+1
    
    while len(workingList) > 0:
        # On récupère l'état de l'automate produit et les deux composants de la paire
        currentS = workingList[0][0]
        currentPair0 = workingList[0][1][0]
        currentPair1 = workingList[0][1][1]
        okList.append(workingList.pop(0))
        for l in alphabet:
            for succPair0 in succElem(auto0,currentPair0,l):
                for succPair1 in succElem(auto1,currentPair1,l):
                    succS = State(0,False,False) #valeur bidon
                    found = False
                    for list in workingList + okList:
                        # Cas où succPair est déjà connu
                        if list[1][0] == succPair0 and list[1][1] == succPair1:
                            succS = list[0]
                            found = True
                    # Cas où succPair est nouveau
                    if not found:
                        succS = State(cpt, False, final(succPair0,succPair1), succPair0.label + succPair1.label)
                        workingList.append([succS,[succPair0,succPair1]])
                        cpt = cpt+1
                    # Ajout de la transition
                    transList.append(Transition(currentS, l, succS))
            
    return AutomateBase(transList)

def union (auto0, auto1):
    """ Automate x Automate -> Automate
    rend l'automate acceptant pour langage l'union des langages des deux automates
    """
    # Pareil que intersection, juste remplacer le and par un or dans la definition de final.
    #   (il faut aussi compléter les deux automates juste avant)
    # Autre façon : juste coller les deux automates, vu qu'on peut avoir plusieurs états initiaux.
    #   (dans ce cas, faire attention à renommer les états pour ne pas avoir de collision entre les deux automates)

    alphabet = auto0.getAlphabetFromTransitions()

    if not estComplet(auto0,alphabet):
        auto0 = completeAutomate(auto0,alphabet)
    if not estComplet(auto1,alphabet):
        auto1 = completeAutomate(auto1,alphabet)

    cpt = 0
    # Même principe que pour determinisation
    workingList = []
    okList = []
    transList = []
    
    def final (s0,s1) :
        return (s0.fin or s1.fin)
    
    # Création des états initiaux de l'automate produit
    for s0 in auto0.getListInitialStates():
        for s1 in auto1.getListInitialStates():
            workingList.append([State(cpt, True, final(s0,s1), s0.label + s1.label),[s0,s1]])
            cpt = cpt+1
    
    while len(workingList) > 0:
        # On récupère l'état de l'automate produit et les deux composants de la paire
        currentS = workingList[0][0]
        currentPair0 = workingList[0][1][0]
        currentPair1 = workingList[0][1][1]
        okList.append(workingList.pop(0))
        for l in alphabet:
            for succPair0 in succElem(auto0,currentPair0,l):
                for succPair1 in succElem(auto1,currentPair1,l):
                    succS = State(0,False,False) #valeur bidon
                    found = False
                    for list in workingList + okList:
                        # Cas où succPair est déjà connu
                        if list[1][0] == succPair0 and list[1][1] == succPair1:
                            succS = list[0]
                            found = True
                    # Cas où succPair est nouveau
                    if not found:
                        succS = State(cpt, False, final(succPair0,succPair1), succPair0.label + succPair1.label)
                        workingList.append([succS,[succPair0,succPair1]])
                        cpt = cpt+1
                    # Ajout de la transition
                    transList.append(Transition(currentS, l, succS))
            
    return AutomateBase(transList)

#####
# Fonctions auxiliaires internes
#####
    
def removeUnreachableStates (auto) :
    """ Automate -> Automate
    retire de auto les états non atteignables
    """
    alphabet = auto.getAlphabetFromTransitions()
    reachable = auto.getListInitialStates()
    next = []
    # calculs des états atteignables
    while next != reachable:
        next = copy.deepcopy(reachable)
        for a in alphabet:
            reachable += [s for s in succ(auto,reachable,a) if s not in reachable]
    # on enlève les autres
    for s in [s for s in auto.listStates if (s not in reachable)]:
        auto.removeState(s)
    return
    
def removeUncoreachableStates (auto) :
    """ Automate -> Automate
    retire de auto les états à partir desquels on ne peut pas atteindre un état final
    """
    alphabet = auto.getAlphabetFromTransitions()
    coreachable = auto.getListFinalStates()
    next = []
    # calculs des états coatteignables
    while next != coreachable:
        next = copy.deepcopy(coreachable)
        for a in alphabet:
            coreachable += [s for s in auto.listStates if (s not in coreachable) and (succElem(auto,s,a) != []) and (succElem(auto,s,a)[0] in coreachable)]
    # on enlève les autres
    for s in [s for s in auto.listStates if (s not in coreachable)]:
        auto.removeState(s)
    return
    
    
def mergeStates (auto) :
    """ Automate -> Automate
    fusionne les états équivalents de auto
    renvoie un nouvel automate
    """
    alphabet = auto.getAlphabetFromTransitions()
    # partition des états : dictionnaire (état -> id de son groupe dans la partition)
    partition = dict.fromkeys(auto.listStates, 0)
    # fonctions de manipulation de partition
    def groupeById (id) :
        return [state for (state,i) in partition.items() if i == id]
    def updateStateId (state,new_id) :
        partition[state] = new_id
        return
    def freshId (p) :
        return max(p.values())+1
    def reachableIdsByState (state, lettre) :
        return [id for id in set(partition.values()) if any((t.etiquette == lettre and partition[t.stateDest] == id) for t in auto.getListTransitionsFrom(state))]
    # initialisation de la partition en séparant final de non final
    for state in auto.listStates:
        if state.fin:
            updateStateId (state,1)
    # boucle principale de séparation de la partition
    separation = True
    i = 0
    while separation:
        i += 1
        #print("Etape numero ", i)
        #print("Partition actuelle : ", partition)
        separation = False
        groupes = [groupeById(id) for id in set(partition.values())]
        #print("Groupes : ", groupes)
        while (not separation) and groupes != []:
            groupe = groupes.pop(0)
            #print("\tGroupe : ", groupe)
            alpha = copy.deepcopy(alphabet)
            while (not separation) and alpha != []:
                lettre = alpha.pop(0)
                #print("\t\tLettre : ", lettre)
                groupeCopy = copy.deepcopy(groupe)
                state = groupeCopy.pop(0)
                # nouvelle partition qui va remplacer l'ancienne
                newPartition = copy.deepcopy(partition)
                # representantDict contient un representant par groupe de la nouvelle partition
                representantsDict = {}
                representantsDict[state] = reachableIdsByState(state,lettre)
                for state in groupeCopy:
                    #print("\t\t\tRepresentantsDict : ", representantsDict)
                    l = reachableIdsByState(state,lettre)
                    aSeparer = True
                    # on cherche si state va être mis dans un groupe déjà existant ...
                    for representant in representantsDict:
                        if testEqualList(representantsDict[representant], l):
                            aSeparer = False
                            newPartition[state] = newPartition[representant]
                    # ... sinon on créé un nouveau groupe dont state sera le représentant
                    if aSeparer:
                        representantsDict[state] = l
                        newPartition[state] = freshId(newPartition)
                        separation = True
                # finalement on met à jour partition si il y a eu au moins une séparation
                if separation:
                    partition = newPartition
    # construction de l'automate minimal à partir de la partition
    ids = list(set(partition.values()))
    # création d'un dictionnaire (id du groupe dans la partition -> état dans l'automate minimal)
    newStatesDict = {}
    for id in ids:
        groupe = groupeById(id)
        newFinal = any(state.fin for state in groupe)
        newInit = any(state.init for state in groupe)
        newLabel = str([s.label for s in groupe])
        newStatesDict[id] = State(id,newInit,newFinal,newLabel)
    # rajout des transitions de l'automate minimal
    newTransitionsList = []
    for idSrc in ids:
        for idDst in ids:
            for lettre in alphabet:
                # si il y a au moins 1 état d'id idDst atteint par une transition d'étiquette lettre partant d'un état d'id idSrc...
                if any((len([t.stateDest for t in auto.getListTransitionsFrom(stateSrc) if t.etiquette == lettre and t.stateDest in groupeById(idDst)]) > 0) for stateSrc in groupeById(idSrc)):
                    # ... alors on ajoute une transition de idSrc vers idDst dans l'automate minimal
                    newTransitionsList.append(Transition(newStatesDict[idSrc],lettre,newStatesDict[idDst]))
    return AutomateBase(newTransitionsList)
    
def minimisation (auto) :
    """ Automate -> Automate
    rend l'automate minimisé reconnaissant le même langage que auto
    suppose que auto est déterministe
    """
    autoDet = determinisation(auto)
    removeUnreachableStates(autoDet)
    removeUncoreachableStates(autoDet)
    return mergeStates(autoDet)
    
def trouverMot (auto) :
    """ Automate -> Bool x String
    rend (True,w) avec w un mot accepté par auto s'il en existe un, (False,"None") sinon
    """
    alphabet = auto.getAlphabetFromTransitions()
    # on affecte à chaque état de l'automate un mot qui amène dans cet état
    workingList = auto.getListInitialStates()
    dico = dict.fromkeys(workingList, "")
    while workingList != []:
        newWorkingList = []
        for a in alphabet:
            for state in workingList:
                for stateDest in succElem(auto, state, a):
                    if not stateDest in dico:
                        dico[stateDest] = dico[state]+a
                        newWorkingList.append(stateDest)
        workingList = newWorkingList
    # puis on récupère un tel mot pour un état final
    for statefinal in auto.getListFinalStates():
        if statefinal in dico:
            if dico[statefinal] == "":
                return (True,"Epsilon")
            else:
                return (True,dico[statefinal])
    return (False,"None")
    
#####
# Fonctions de tests (utilisables à l'extérieur de ce fichier)
#####

def testEqualList (l, m) :
    def aux (l1, l2) :
        if len(l1) == 0 and len(l2) == 0:
            return True
        elif len(l1) == 0 or len(l2) == 0:
            return False
        else:
            e = l1[0]
            if e in l2:
                l1.remove(e)
                l2.remove(e)
                return aux (l1, l2)
            else:
                return False
    return aux (copy.deepcopy(l), copy.deepcopy(m))

def testEstComplet(auto,alphabet) :
    return estComplet(auto,alphabet)
    
def testEstDeterministe(auto) :
    return estDeterministe(auto)

def testEqualAutoMini (auto1, auto2) :
    """ Automate^2 -> Bool
    Teste l'égalité de langages de deux automates par bijection des automates minimisés
    """
    alphabet = auto1.getAlphabetFromTransitions()
    auto1m = minimisation(auto1)
    auto2m = minimisation(auto2)
    states1 = auto1m.listStates
    states2 = auto2m.listStates
    if len(states1) != len(states2):
        # print("Automates minimaux de tailles différentes")
        return False
    # Génération de toutes les bijections possibles des états du 1 vers les états du 2
    listePerm = [list(zip(x,states2)) for x in list(itertools.permutations(states1))]
    # On enlève les permutations qui ne matchent pas les états initiaux/finaux avec des états initiaux/finaux
    listePerm = [perm for perm in listePerm if not any(True for (s1,s2) in perm if ((s1.fin != s2.fin) or (s1.init != s2.init)))]
    # On enlève les permutations telles qu'il existe (s1,s2) dans perm avec (s1.a,s2.a) pas dans perm pour une lettre a 
    def isValid (perm):
        for (s1,s2) in perm:
            for a in alphabet:
                succ1 = succElem(auto1m, s1, a)
                succ2 = succElem(auto2m, s2, a)
                if len(succ1) != len(succ2):
                    return False
                if len(succ1) > 0 and (succ1[0], succ2[0]) not in perm:
                    return False
        return True
    listePerm = [perm for perm in listePerm if isValid (perm)]
    # On renvoie vrai ssi il reste au moins une permutation
    return len(listePerm) > 0
    
def testEqualAuto (auto1, auto2) :
    """ Automate^2 -> Bool
    Teste l'égalité de langages de deux automates par vide de la différence symmétrique
    """
    alphabet = auto1.getAlphabetFromTransitions()
    auto1c = complementaire(auto1, alphabet)
    auto2c = complementaire(auto2, alphabet)
    auto1moins2 = intersection(auto1,auto2c)
    auto2moins1 = intersection(auto2,auto1c)
    # Création de l'automate de la différence symmétrique
    autodiff = union(auto1moins2, auto2moins1)
    # Recherche d'un mot accepté
    (found, w) = trouverMot(autodiff)
    # Renvoie vrai si le langage de l'automate est vide
    return not found

def testFindDifference (auto1, auto2) :
    """ Automate^2 -> String
    Renvoie un mot accepté par l'un des automates mais pas l'autre
    """
    alphabet = auto1.getAlphabetFromTransitions()
    auto1c = complementaire(auto1, alphabet)
    auto2c = complementaire(auto2, alphabet)
    auto1moins2 = intersection(auto1,auto2c)
    auto2moins1 = intersection(auto2,auto1c)
    # Création de l'automate de la différence symmétrique
    autodiff = union(auto1moins2, auto2moins1)
    # Recherche d'un mot accepté
    (found, w) = trouverMot(autodiff)
    return w
    


########
# Tests
########

# auto1 reconnait les mots sur {a,b} ayant un nombre impair de a 
# Déterministe/Complet

s01 = State(0,True,False)
s11 = State(1,False,True)
auto1 = AutomateBase([Transition(s01,'b',s01),Transition(s01,'a',s11),Transition(s11,'b',s11),Transition(s11,'a',s01)])

# auto2 reconnait les mots de la forme a*b*
# Déterministe/Non Complet

s02 = State(0,True,True)
s12 = State(1,False,True)
auto2 = AutomateBase([Transition(s02,'a',s02),Transition(s02,'b',s12),Transition(s12,'b',s12)])

# auto3 reconnait les mots avec 2 a consécutifs
# ND/NC

s03 = State(0,True,False)
s13 = State(1,False,False)
s23 = State(2,False,True)
auto3 = AutomateBase([Transition(s03,'a',s03),Transition(s03,'b',s03),Transition(s03,'a',s13),Transition(s13,'a',s23),Transition(s23,'a',s23),Transition(s23,'b',s23)])

# auto4 reconnait les mots contenant (au moins) un a
# ND/C

s04 = State(0,True,False)
s14 = State(1,False,True)
auto4 = AutomateBase([Transition(s04,'a',s04),Transition(s04,'b',s04),Transition(s04,'a',s14),Transition(s14,'a',s14),Transition(s14,'b',s14)])

# auto5 reconnait les mots commençant par un b (avec deux états initiaux)
# ND/C

s05 = State(0,True,False)
s15 = State(1,True,False)
s25 = State(2,False,True)
s35 = State(3,False,False)
auto5 = AutomateBase([Transition(s05,'a',s35),Transition(s15,'a',s35),Transition(s05,'b',s25),Transition(s15,'b',s35),Transition(s25,'a',s25),Transition(s25,'b',s25),Transition(s35,'a',s35),Transition(s35,'b',s35)])

#
s1t = State(0,True,False)
s2t = State(1,False,False)
s3t = State(2,False,False)
s4t = State(3,False,True)
autot = AutomateBase([Transition(s1t,'a',s2t),Transition(s1t,'b',s3t),Transition(s2t,'b',s4t),Transition(s3t,'b',s4t)])

#
s1r = State(0,True,False)
s2r = State(1,False,False)
s3r = State(2,False,True)
s4r = State(3,False,True)
s5r = State(4,False,True)
s6r = State(5,False,False)
autor = AutomateBase([Transition(s1r,'0',s2r),Transition(s1r,'1',s3r),Transition(s2r,'0',s1r),Transition(s2r,'1',s4r),Transition(s3r,'0',s5r),Transition(s3r,'1',s6r),Transition(s4r,'0',s5r),Transition(s4r,'1',s6r),Transition(s5r,'0',s5r),Transition(s5r,'1',s6r),Transition(s6r,'0',s6r),Transition(s6r,'1',s6r)])

# Equivalent à auto4
auto4bis = AutomateBase([Transition(s04,'b',s04),Transition(s04,'a',s14),Transition(s14,'a',s14),Transition(s14,'b',s14)])
# Equivalent à auto5
auto5bis = AutomateBase([Transition(s04,'b',s14),Transition(s14,'b',s14),Transition(s14,'a',s14)])
# Equivalent à auto4
s1a = State(0,True,False)
s2a = State(1,False,True)
s3a = State(2,False,True)
s4a = State(3,False,False)
auto4ter = AutomateBase([Transition(s1a,'b',s1a),Transition(s1a,'a',s2a),Transition(s2a,'b',s2a),Transition(s2a,'a',s3a),Transition(s3a,'b',s3a),Transition(s3a,'a',s2a),Transition(s4a,'a',s2a),Transition(s4a,'b',s3a)])

s1b = State(0,True,False)
s2b = State(1,False,True)
s3b = State(2,False,False)
automod3 = AutomateBase([Transition(s1b,'a',s2b),Transition(s2b,'a',s3b),Transition(s3b,'a',s1b),Transition(s1b,'b',s1b),Transition(s2b,'b',s2b),Transition(s3b,'b',s3b)])
s4b = State(3,False,False)
s5b = State(4,False,True)
s6b = State(5,False,False)
automod3bis = AutomateBase([Transition(s1b,'a',s2b),Transition(s2b,'a',s3b),Transition(s3b,'a',s4b),Transition(s4b,'a',s5b),Transition(s5b,'a',s6b),Transition(s6b,'a',s1b),Transition(s1b,'b',s1b),Transition(s2b,'b',s2b),Transition(s3b,'b',s3b),Transition(s4b,'b',s4b),Transition(s5b,'b',s5b),Transition(s6b,'b',s6b)])

s1v = State(0,True,False)
autovide = AutomateBase([Transition(s1v,'a',s1v)])

if False: 
    # auto4d = determinisation(auto4)
    # auto4bd = determinisation(auto4bis)
    # auto4m = minimisation(auto4d)
    # auto4bm = minimisation(auto4bd)
    # print(auto4m)
    # print(auto4bm)
    assert(testEqualAuto(auto4,auto4bis)) ## True
    assert(not testEqualAuto(auto1,auto2)) ## False
    # auto5m = minimisation(determinisation(auto5))
    # auto5bm = minimisation(determinisation(auto5bis))
    # print(auto5m)
    # print(auto5bm)
    assert(testEqualAuto(auto5,auto5bis)) ## True
    # auto1d = determinisation(auto1)
    # print(auto1d)
    # auto5bd = determinisation(auto5bis)
    # print(auto5bd)
    # removeUncoreachableStates(auto5bd)
    # print(auto5bd)
    # print(minimisation(determinisation(auto1)))
    # print(minimisation(determinisation(auto5bis)))
    assert(not testEqualAuto(auto1,auto5bis)) ## False
    # print(minimisation(auto4))
    # print(minimisation(auto4ter))
    assert(testEqualAuto(auto4,auto4ter)) ## True
    # print(minimisation(automod3))
    # print(minimisation(automod3bis))
    assert(testEqualAuto(automod3,automod3bis)) ## True
    assert(not testEqualAuto(automod3,auto1)) ## False
    assert(not testEqualAuto(automod3,auto2)) ## False
    assert(not testEqualAuto(automod3,auto3)) ## False
    assert(not testEqualAuto(automod3,auto4)) ## False
    assert(not testEqualAuto(automod3,auto5)) ## False
    # print(minimisation(autovide))
    # print(testFindDifference(auto4,auto4bis))
    # print(testFindDifference(auto1,auto2))
    # print(testFindDifference(auto5,auto5bis))
    # print(testFindDifference(auto1,auto5bis))
    # print(testFindDifference(auto4,auto4ter))
    # print(testFindDifference(automod3,automod3bis))
    # print(testFindDifference(automod3,auto1))
    # print(testFindDifference(automod3,auto2))
    print("Tests ok.")

# Fin tests  