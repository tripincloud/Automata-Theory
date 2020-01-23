# -*- coding: utf-8 -*-
from transition import *
from state import *
import os
import copy
from sp import *
from parser import *
from itertools import product
from automateBase import AutomateBase



class Automate(AutomateBase):

    def succElem(self, state, lettre):
        """State x str -> list[State]
        rend la liste des états accessibles à partir d'un état
        state par l'étiquette lettre
        """
        successeurs = []
        # t: Transitions
        for t in self.getListTransitionsFrom(state):
            if (t.etiquette == lettre) and (t.stateDest not in successeurs):
                successeurs.append(t.stateDest)

        return successeurs


    def succ (self, listStates, lettre):
        """list[State] x str -> list[State]
        rend la liste des états accessibles à partir de la liste d'états
        listStates par l'étiquette lettre
        """
        L=[]
        s=[]
        for e in listStates :
            	s=s+self.succElem(e,lettre)
        for i in s :
            	if i not in L :
        		    L.append(i)
        return L






    """ Définition d'une fonction déterminant si un mot est accepté par un automate.
    Exemple :
            a=Automate.creationAutomate("monAutomate.txt")
            if Automate.accepte(a,"abc"):
                print "L'automate accepte le mot abc"
            else:
                print "L'automate n'accepte pas le mot abc"
    """
    @staticmethod
    def accepte(auto,mot):
        """ Automate x str -> bool
        rend True si auto accepte mot, False sinon
        """

        states = auto.getListInitialStates()

        for i in mot:
            states=auto.succ(states,i)

        for s in states:
        	if s.fin == True:
        		return True
        return False


    @staticmethod
    def estComplet(auto,alphabet) :
        """ Automate x str -> bool
         rend True si auto est complet pour alphabet, False sinon
        """
        listStates = Automate.getListInitialStates(auto)
        listsucc = []
        for state in listStates :
            for lettre in alphabet :
                if auto.succElem(state, lettre) == [] :
                    return False
                else :
                    for s  in auto.succElem(state, lettre):
                        if s not in listStates :
                            listStates.append(s)
        return True

    @staticmethod
    def estDeterministe(auto) :
        """ Automate  -> bool
        rend True si auto est déterministe, False sinon
        """
        alphabet=auto.getAlphabetFromTransitions()
        Lini=auto.getListInitialStates()
        if len(Lini) > 1:
            return False

        for lettre in alphabet:
            for state in Lini:
                if len(auto.succElem(state,lettre)) > 1:
                    return False
                Lini=auto.succ(Lini,lettre)
        return True



    @staticmethod
    def completeAutomate(auto,alphabet) :
        """ Automate x str -> Automate
        rend l'automate complété d'auto, par rapport à alphabet
        """

        if (auto.estComplet(auto,alphabet)) :
            return auto

        a = copy.deepcopy(auto)
        #if (Automate.estComplet(auto,alphabet)) :
        #    return a
        L= auto.listStates
        #creation d'un puit
        listeid= [s.id for s in auto.listStates]
        condition =True
        i=0
        while (condition):
            if i in listeid:
                i+=1
            else:
                condition =False


        puit = State(i,False,False,"puit")
        auto.addState(puit)

        # ajout de toute les transitions du puit vers le puit
        for lettre in alphabet :
        	a.addTransition(Transition(puit, lettre, puit))


        for s in L:
            Lt=auto.getListTransitionsFrom(s)
            LettreLt=[k.etiquette for k in Lt]
            for lettre2 in alphabet:
            		if lettre2 not in LettreLt: #verfication + ajout si il en manque une
            			a.addTransition(Transition(s, lettre2, puit))
        return a


    @staticmethod
    def determinisation(auto) :

        #copie de l'automate + verification si il est deja deterministe
        if Automate.estDeterministe(auto):
            return auto

        triEtat   = lambda etat : etat.id
        alphabet  = auto.getAlphabetFromTransitions()
        A = Automate([])
        Letatsini = auto.getListInitialStates()
        Letatsini.sort(key=triEtat)
        Letatajouter = [Letatsini]
        init = True
        while(len(Letatajouter) > 0):
            print(Letatajouter)
            etats = Letatajouter.pop()
            s = State(etats[0].id,init,State.isFinalIn(etats))
            init = False
            for etat in etats[1:] :
                s.insertPrefix(etat.id)

            for etiquette in alphabet:
                EtatsArrive = auto.succ(etats,etiquette) #Listed'états

                if(len(EtatsArrive) == 0): continue

                EtatsArrive.sort(key = triEtat)
                sArrive=State(EtatsArrive[0].id,False,State.isFinalIn(EtatsArrive))
                for etat in EtatsArrive[1:] :
                    sArrive.insertPrefix(etat.id) #Etat
                if(sArrive not in A.listStates) : Letatajouter.append(EtatsArrive)
                A.addTransition(Transition(s,etiquette,sArrive))
        return A

    @staticmethod
    def complementaire(auto,alphabet):
        """ Automate -> Automate
        rend  l'automate acceptant pour langage le complémentaire du langage de a
        """
        #a=auto.completeAutomate(auto.determinisation(copy.deepcopy(auto)),alphabet)
        a=Automate.determinisation(auto)
        liste=a.listStates
        cpt=1
        for state in liste:
            state.id=cpt
            cpt+=1

        a2=a.completeAutomate(a,alphabet)
        Liste= a2.listStates

        for l in Liste:
            if (l.fin): #si l'etat est final, changement
                l.fin = False
            else:
		#if (not l.init):  si l'etat n'est pas inital + pas final , changement
                l.fin=True
        return a2


    @staticmethod
    def intersection (auto0, auto1):
        """ Automate x Automate -> Automate
        rend l'automate acceptant pour langage l'intersection des langages des deux automates
        """

        #determination des automates 0 et 1
        A0=Automate.determinisation(auto0)
        A1=Automate.determinisation(auto1)
	    #etats initiaux de a0 et a1
        L0=A0.getListInitialStates()
        L1=A1.getListInitialStates()

	    #liste des tuples des differents etats
        Lcouple= []

	    #listes des etats
        Letat = []

	    #liste des transitions
        Ltransition=[]
        cpt=0

	    #l'alphabet
        alphabet=auto1.getAlphabetFromTransitions()

        #creation la liste de tuples des etats initiaux
        for etat in L0:
            	for state in L1:
            		Lcouple.append((etat,state))
            		Letat.append(State(cpt,True,(etat.fin and state.fin),etat.label+" "+state.label))
            		cpt+=1


        #creation de la liste d'etats
        for etat1,etat2 in Lcouple:
            	for lettre in alphabet:
    			#on ne veut que l'etat suivant
            		etatsuivant1=A0.succElem(etat1,lettre)[0]
            		etatsuivant2=A1.succElem(etat2,lettre)[0]
            		etatsuivant=(etatsuivant1,etatsuivant2)
            		if etatsuivant not in Lcouple: # verifie si le couple n'est pas dans la liste de tuple
            			Lcouple.append(etatsuivant)
            			Letat.append(State(cpt,False,(etatsuivant1.fin and etatsuivant2.fin),etatsuivant1.label+","+etatsuivant2.label))
            			cpt+=1


        #creation de la liste de transition
        for i in range(0,len(Lcouple)):
            	etat1,etat2=Lcouple[i]
            	for lettre in alphabet:
    			#on ne veut que l'etat suivant
            		etatsuivant1=A0.succElem(etat1,lettre)[0]
            		etatsuivant2=A1.succElem(etat2,lettre)[0]
            		etatsuivant=(etatsuivant1,etatsuivant2)#creation du tuple
            		for j in range(0,len(Lcouple)): #verifique qu'il ne soit pas dans la liste
            			if Lcouple[j]==etatsuivant and (Transition(Letat[i],lettre,Letat[j]) not in Ltransition):
            				Ltransition.append(Transition(Letat[i],lettre,Letat[j]))


        return Automate(Ltransition,Letat)

    @staticmethod
    def union (auto0, auto1):
        """ Automate x Automate -> Automate
        rend l'automate acceptant pour langage l'union des langages des deux automates
        """

        autoc1=copy.deepcopy(auto1)
        autoc2=copy.deepcopy(auto2)

        #liste des transitions
        lft=[]

        alp=auto1.getAlphabetFromTransitions()
        lini=autoc2.getListInitialStates()
        #Listes des etats
        ls1=auto1.listStates
        ls2=auto2.listStates
        #Compteur pour les identifiant
        cpt=0
        #Ajouter les etats au nv automate
        for state in ls2:
            while cpt in [s.id for s in autoc1.listStates]:
                cpt+=1
            state.id = cpt
            autoc1.addState(state)

        #Ajouter les transition au nv automate
        for state in ls2:
            listT=auto2.getListTransitionsFrom(state)
            for t in listT:
                autoc1.addTransition(t)


        #Creation d'un nouvel etat initial
        listeid= [s.id for s in autoc1.listStates]
        condition =True
        i=1
        while (condition):
            if i in listeid:
                i+=1
            else:
                condition =False

        s0 = State(id = i,init = True, fin = False,label = "Init")
        autoc1.addState(s0)


        ini1=autoc1.getListInitialStates()
        ini2=auto2.getListInitialStates()
        #Ajouter les transitions du noouvel etat initial les etats successeurs des etats initiaux
        for s in ini1:
            li1=autoc1.getListTransitionsFrom(s)
            for t in li1:
                autoc1.addTransition(Transition(s0,t.etiquette,t.stateDest))
                t.stateSrc.init=False

        for s in ini2:
            li2=autoc1.getListTransitionsFrom(s)
            for t in li2:
                autoc1.addTransition(Transition(s0,t.etiquette,t.stateDest))
                t.stateSrc.init=False

        return autoc1


    @staticmethod
    def concatenation (auto1, auto2):
        """ Automate x Automate -> Automate
        rend l'automate acceptant pour langage la concaténation des langages des deux automates
        """
        #copy des automates
        autoc1=copy.deepcopy(auto1)
        autoc2=copy.deepcopy(auto2)

        #liste des transitions
        lft=[]

        cpt=0
        alp=auto1.getAlphabetFromTransitions()
        lini=autoc2.getListInitialStates()
        #Listes des etats
        ls1=auto1.listStates
        ls2=auto2.listStates

        #Ajouter les etats et transition de auto2 a auto1
        for state in ls2:
            while cpt in [s.id for s in autoc1.listStates]:
                cpt+=1
            state.id = cpt
            autoc1.addState(state)

        for state in ls2:
            listT=auto2.getListTransitionsFrom(state)
            for t in listT:
                autoc1.addTransition(t)

        for state in ls1:
            if state.fin and state.init:
                for lettre in alp:
                    for i in lini:
                        autoc1.addTransition(Transition(state,lettre,i))

            lft=auto1.getListTransitionsFrom(state)
            for t in lft:
                if t.stateDest.fin :
                    for l in lini:
                        autoc1.addTransition(Transition(t.stateSrc,t.etiquette,l))

        return autoc1



    @staticmethod
    def etoile (auto):
        """ Automate  -> Automate
        rend l'automate acceptant pour langage l'étoile du langage de a
        """

        #auto1 : Automate
        auto1 = copy.deepcopy(auto.determinisation(auto))

        #Liste des etats finaux
        final = []

        #Liste des etats
        listeEtats = auto1.listStates

        #etat : State
        #On met les etats initiaux finaux
        for etat in listeEtats :
            if etat.fin and not(etat.init):
                final.append(etat)
            if etat.init :
                etat.fin = True
                init = etat

        #transitionInit : list[State]
        tInit = auto1.getListTransitionsFrom(init)

        #t : Transition
        #On ajoute les transitions qui vont de l'etat finale vers l'etat destinataire des etats initiaux
        for t in tInit:
	        #e : State
            for e in final:
                auto1.addTransition(Transition(e, t.etiquette, t.stateDest))

        return auto1
#-------------------------------------------------------------------#
"""
## création d’ ́etats
s1 = State(1,True,False)
s2 = State(2, False, False)
s3 = State(3,False,True)

#------------------------------------------------------------------#

## création de transitions
t1 = Transition(s1,"a",s1)
t2 = Transition(s1,"a",s2)
t3 = Transition(s1,"b",s2)
t4 = Transition(s2,"a",s2)
t5 = Transition(s2,"b",s3)
t6 = Transition(s3,"b",s3)
t7 = Transition(s3,"b",s2)
t8 = Transition(s2,"a",s3)
t9 = Transition(s3,"b",s3)



t10= Transition(s1,"a",s1)
t11= Transition(s1,"b",s2)
t12= Transition(s2,"b",s2)
t13= Transition(s2,"a",s3)
t14= Transition(s3,"a",s3)
t15= Transition(s3,"b",s3)

liste1=[t10,t11,t12,t13,t14,t15]

t16= Transition(s1,"a",s1)
t17= Transition(s1,"a",s2)
t18= Transition(s1,"b",s1)
t19= Transition(s2,"b",s3)
t20= Transition(s3,"a",s3)
t21= Transition(s3,"b",s3)

liste2=[t16,t17,t18,t19,t20,t21]


auto1=Automate(listStates =[], label = "auto1", listTransitions = liste1)
auto2=Automate(listStates =[], label = "auto2", listTransitions = liste2)

#------------------------------------------------------------------#

# liste : list[Transition]
liste = [t1,t2,t3,t4,t5,t6,t7]
#liste = [t3,t4,t8,t5]
#liste = [t1,t2,t4,t8]
#------------------------------------------------------------------#

#creation de l’automate

auto=Automate(listStates =[], label = "auto", listTransitions = liste)
#print(auto.succ([s1,s2],'a'))

#auto.show('Avant')
#auto1.show('auto1')
#auto2.show('auto2')

#-------------------------------------------------------------------#

#Test fonction est accepte
if (auto1.accepte(auto1,'a')):
	print("est accepte")
else:
	print("n'est pas accepte")

#-------------------------------------------------------------------#
#Fonctionne

#Test la Determinisation
#auto=auto.determinisation(auto)
#auto.show('deterministe')


#-------------------------------------------------------------------#

#Test si l'automate est Complet

if (auto1.estComplet(auto1,auto1.getAlphabetFromTransitions())):
	print("Est complet")
else:
	print("Pas complet")

#-------------------------------------------------------------------#

#Test si l'automate est DETERMINISTE

if (auto1.estDeterministe(auto1)):
	print("Deterministe")
else:
	print("Non deterministe")

#-------------------------------------------------------------------#


#auto=auto.completeAutomate(auto,'ab')
#auto.show('Complet')

#-------------------------------------------------------------------#

#print(auto.succElem(s3,'a'))

#-------------------------------------------------------------------#

#auto=auto.complementaire(auto,'ab')
#auto.show('Complem')
#-------------------------------------------------------------------#

#auto=auto.etoile(auto)
#auto.show('Etoile')

#-------------------------------------------------------------------#

#auto=Automate.intersection(auto1,auto2)
#auto.show('Inter')

#-------------------------------------------------------------------#

#auto=Automate.concatenation(auto2,auto1)
#auto.show('Concat')


auto=Automate.union(auto1,auto2)
auto.show('Union')
"""
