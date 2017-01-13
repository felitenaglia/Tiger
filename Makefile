# Unix makefile for tigermain example

### LabBasica

#HOME=/home/alumno
#MOSMLHOME=${HOME}/mosml
#MOSMLTOOLS=${MOSMLHOME}/bin/camlrunm $(MOSMLHOME)/tools

### Casa

HOME=/home/felipe
MOSMLHOME=/usr
MOSMLTOOLS=${MOSMLHOME}/bin/camlrunm $(MOSMLHOME)/share/mosml/tools

MOSMLLEX=${MOSMLHOME}/bin/mosmllex
MOSMLYACC=${MOSMLHOME}/bin/mosmlyac -v

GCC=gcc
CFLAGS= -g
MOSMLC=${MOSMLHOME}/bin/mosmlc -c -liberal
MOSMLL=${MOSMLHOME}/bin/mosmlc

# Unix
REMOVE=rm -f
MOVE=mv
EXEFILE=

# DOS
#REMOVE=del
#MOVE=move
#EXEFILE=.exe

.SUFFIXES :
.SUFFIXES : .sig .sml .ui .uo

GRALOBJS= tigerabs.uo tigergrm.uo tigerlex.uo tigermain.uo \
	tigernlin.uo tigerpp.uo tigerescap.uo tigertab.uo tigerseman.uo tigertemp.uo topsort.uo tigertopsort.uo tigertree.uo \
 	tigerframe.uo tigertrans.uo tigerit.uo tigerpila.uo tigerinterp.uo \
        tigercanon.uo tigercodegen.uo tigerassem.uo tigergraph.uo tigerflowgraph.uo tigerliveness.uo tigerregister.uo

all: tiger

tiger: $(GRALOBJS) $(OBJSGEN)
	$(MOSMLL) -o tiger $(EXEFILE) tigermain.uo

tigergrm.sml tigergrm.sig: tigergrm.y 
	$(MOSMLYACC) tigergrm.y

tigerlex.sml: tigerlex.lex
	$(MOSMLLEX) tigerlex.lex

clean:
	$(REMOVE) Makefile.bak
	$(REMOVE) tigergrm.output
	$(REMOVE) tigergrm.sig
	$(REMOVE) tigergrm.sml
	$(REMOVE) tigerlex.sml
	$(REMOVE) tiger
	$(REMOVE) *.ui
	$(REMOVE) *.uo
	$(REMOVE) errlist
	$(REMOVE) *.o

.sig.ui:
	$(MOSMLC) $<

.sml.uo:
	$(MOSMLC) $<

depend: tigerabs.sml tigergrm.sml tigerlex.sml tigermain.sml \
	tigernlin.sml tigerpp.sml tigertopsort.sml
	$(REMOVE) Makefile.bak
	$(MOVE) Makefile Makefile.bak
	$(MOSMLTOOLS)/cutdeps < Makefile.bak > Makefile
	$(MOSMLTOOLS)/mosmldep >> Makefile

### DO NOT DELETE THIS LINE
tigerpp.uo: tigerabs.uo 
tigercanon.uo: tigercanon.ui tigertree.uo tigertab.ui tigertemp.ui 
tigermain.uo: tigerseman.ui tigercodegen.ui tigerescap.ui tigergrm.ui \
    tigerframe.ui tigerit.uo tigercanon.ui tigerassem.uo tigerinterp.uo \
    tigerlex.uo tigertrans.ui tigerpp.uo tigerregister.ui 
tigerlex.uo: tigergrm.ui tigernlin.uo 
tigerpila.uo: tigerpila.ui 
tigerescap.ui: tigerabs.uo 
tigercodegen.ui: tigertree.uo tigerframe.ui tigerassem.uo 
tigerit.uo: tigertree.uo tigertab.ui 
tigerflowgraph.ui: tigergraph.ui tigerassem.uo tigertemp.ui 
tigerregister.ui: tigerframe.ui tigerassem.uo tigertemp.ui 
tigergraph.uo: tigergraph.ui tigertemp.ui 
tigerseman.ui: tigerabs.uo 
tigercanon.ui: tigertree.uo tigertemp.ui 
tigerinterp.uo: tigertree.uo tigertab.ui tigerframe.ui tigerit.uo \
    tigertemp.ui 
tigerliveness.uo: tigerliveness.ui tigergraph.ui tigertemp.ui \
    tigerflowgraph.ui 
tigerregister.uo: tigerregister.ui tigercodegen.ui tigergraph.ui \
    tigerframe.ui tigerassem.uo tigertemp.ui tigerflowgraph.ui \
    tigerliveness.ui 
tigerframe.uo: tigerframe.ui tigertree.uo tigerassem.uo tigertemp.ui 
tigercodegen.uo: tigercodegen.ui tigertree.uo tigerframe.ui tigerit.uo \
    tigerassem.uo tigertemp.ui 
tigertab.uo: tigertab.ui 
tigerassem.uo: tigertemp.ui 
tigerflowgraph.uo: tigerflowgraph.ui tigertab.ui tigergraph.ui \
    tigerassem.uo tigertemp.ui 
tigertrans.uo: tigertrans.ui tigertree.uo tigerpila.ui tigerframe.ui \
    tigerit.uo tigertemp.ui tigerabs.uo 
tigertopsort.uo: tigertopsort.ui tigersres.uo tigerabs.uo 
tigersres.uo: tigertab.ui tigertips.uo tigertemp.ui tigerabs.uo \
    tigertrans.ui 
tigertrans.ui: tigertree.uo tigerframe.ui tigertemp.ui tigerabs.uo 
tigerseman.uo: tigerseman.ui tigersres.uo tigertab.ui tigerpila.ui \
    tigertopsort.ui tigertemp.ui tigerabs.uo tigertrans.ui 
tigergrm.uo: tigergrm.ui tigernlin.uo tigerabs.uo 
tigerescap.uo: tigerescap.ui tigertab.ui tigerabs.uo 
tigerliveness.ui: tigergraph.ui tigertemp.ui tigerflowgraph.ui 
tigertree.uo: tigertemp.ui 
tigergrm.ui: tigerabs.uo 
tigertopsort.ui: tigertab.ui tigertips.uo tigerabs.uo 
tigerframe.ui: tigertree.uo tigerassem.uo tigertemp.ui 
tigertemp.uo: tigertemp.ui 
