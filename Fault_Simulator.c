/*=======================================================================
  A simple parser for "self" format

  The circuit format (called "self" format) is based on outputs of
  a ISCAS 85 format translator written by Dr. Sandeep Gupta.
  The format uses only integers to represent circuit information.
  The format is as follows:

1        2        3        4           5           6 ...
------   -------  -------  ---------   --------    --------
0 GATE   outline  0 IPT    #_of_fout   #_of_fin    inlines
                  1 BRCH
                  2 XOR(currently not implemented)
                  3 OR
                  4 NOR
                  5 NOT
                  6 NAND
                  7 AND

1 PI     outline  0        #_of_fout   0

2 FB     outline  1 BRCH   inline

3 PO     outline  2 - 7    0           #_of_fin    inlines




                                    Author: Chihang Chen
                                    Date: 9/16/94

=======================================================================*/

#include <stdio.h>
#include <ctype.h>
#include <stdlib.h>
#include <stdbool.h>

#define MAXLINE 81               /* Input buffer size */
#define MAXNAME 31               /* File name size */

#define Upcase(x) ((isalpha(x) && islower(x))? toupper(x) : (x))
#define Lowcase(x) ((isalpha(x) && isupper(x))? tolower(x) : (x))

enum e_com {READ, PC, HELP, QUIT, LEV};
enum e_state {EXEC, CKTLD};         /* Gstate values */
enum e_ntype {GATE, PI, FB, PO};    /* column 1 of circuit format */
enum e_gtype {IPT, BRCH, XOR, OR, NOR, NOT, NAND, AND};  /* gate types */

struct cmdstruc {
   char name[MAXNAME];        /* command syntax */
   int (*fptr)();             /* function pointer of the commands */
   enum e_state state;        /* execution state sequence */
};

typedef struct n_struc {
   unsigned indx;             /* node index(from 0 to NumOfLine - 1 */
   unsigned num;              /* line number(May be different from indx */
   enum e_gtype type;         /* gate type */
   unsigned fin;              /* number of fanins */
   unsigned fout;             /* number of fanouts */
   struct n_struc **unodes;   /* pointer to array of up nodes */
   struct n_struc **dnodes;   /* pointer to array of down nodes */
   int level;                 /* level of the gate output */
   bool islevel;
   int node_value;            /* value of node:0,1,2(fault free),3(either SA1 or SA0) */
   int *L;                    /* fault list of each node */
} NSTRUC;                     

typedef struct fl_struc {
   unsigned indx;             /* node index, Node[indx] */
   bool s_a_0;                /* Stuck-at-0 fault*/
   bool s_a_1;                /* Stuck-at-1 fault*/
} FAULTLIST;

/*----------------- Command definitions ----------------------------------*/
#define NUMFUNCS 9
int cread(), pc(), help(), quit(), lev(), preprocessor(), pfs(),fault_free_simulation();
int  deductive_fault_simulation();
int* union_op(int *x, int *y);
int* intersaction_op(int *x, int *y);
int* minus_op(int *x, int *y);
int fault_list_propogate(NSTRUC* np);
struct cmdstruc command[NUMFUNCS] = {
   {"READ", cread, EXEC},
   {"PC", pc, CKTLD},
   {"HELP", help, EXEC},
   {"QUIT", quit, EXEC},
   {"LEV", lev, CKTLD},
   {"GFL", preprocessor, CKTLD},
   {"PFS", pfs, CKTLD},
   {"DFS", deductive_fault_simulation, CKTLD},
   {"FFS", fault_free_simulation, CKTLD},
};

/*------------------------------------------------------------------------*/
enum e_state Gstate = EXEC;     /* global exectution sequence */
NSTRUC *Node;                   /* dynamic array of nodes */
NSTRUC **Pinput;                /* pointer to array of primary inputs */
NSTRUC **Poutput;               /* pointer to array of primary outputs */
int Nnodes;                     /* number of nodes */
int Npi;                        /* number of primary inputs */
int Npo;                        /* number of primary outputs */
int Done = 0;                   /* status bit to terminate program */
int Maxlevel; 
int count = 0;                  /* maximum value of levelization */
FAULTLIST *CompleteFL;          /* complete single stuck-at-fault fault list */
FAULTLIST *CollapsedFL;         /* collapsed fault list */
/*------------------------------------------------------------------------*/

/*-----------------------------------------------------------------------
input: nothing
output: nothing
called by: shell
description:
  This is the main program of the simulator. It displays the prompt, reads
  and parses the user command, and calls the corresponding routines.
  Commands not reconized by the parser are passed along to the shell.
  The command is executed according to some pre-determined sequence.
  For example, we have to read in the circuit description file before any
  action commands.  The code uses "Gstate" to check the execution
  sequence.
  Pointers to functions are used to make function calls which makes the
  code short and clean.
-----------------------------------------------------------------------*/
main()
{
   enum e_com com;
   char cline[MAXLINE], wstr[MAXLINE], *cp;
   cread("c17.ckt");
   lev();
   fault_free_simulation();

   while(!Done) {
      printf("\nCommand>");
      fgets(cline, MAXLINE, stdin);
      if(sscanf(cline, "%s", wstr) != 1) continue;
      cp = wstr;
      while(*cp){
  *cp= Upcase(*cp);
  cp++;
      }
      cp = cline + strlen(wstr);
      com = READ;
      while(com < NUMFUNCS && strcmp(wstr, command[com].name)) com++;
      if(com < NUMFUNCS) {
         if(command[com].state <= Gstate) (*command[com].fptr)(cp);
         else printf("Execution out of sequence!\n");
      }
      else system(cline);
   }
}

/*-----------------------------------------------------------------------
input: circuit description file name
output: nothing
called by: main
description:
  This routine reads in the circuit description file and set up all the
  required data structure. It first checks if the file exists, then it
  sets up a mapping table, determines the number of nodes, PI's and PO's,
  allocates dynamic data arrays, and fills in the structural information
  of the circuit. In the ISCAS circuit description format, only upstream
  nodes are specified. Downstream nodes are implied. However, to facilitate
  forward implication, they are also built up in the data structure.
  To have the maximal flexibility, three passes through the circuit file
  are required: the first pass to determine the size of the mapping table
  , the second to fill in the mapping table, and the third to actually
  set up the circuit information. These procedures may be simplified in
  the future.
-----------------------------------------------------------------------*/
cread(cp)
char *cp;
{
   char buf[MAXLINE];
   int ntbl, *tbl, i, j, k, nd, tp, fo, fi, ni = 0, no = 0;
   FILE *fd;
   NSTRUC *np;

   sscanf(cp, "%s", buf);
   if((fd = fopen(buf,"r")) == NULL) {
      printf("File %s does not exist!\n", buf);
      return;
   }
   if(Gstate >= CKTLD) clear();
   Nnodes = Npi = Npo = ntbl = 0;
   while(fgets(buf, MAXLINE, fd) != NULL) {
      if(sscanf(buf,"%d %d", &tp, &nd) == 2) {
         if(ntbl < nd) ntbl = nd;
         Nnodes ++;
         if(tp == PI) Npi++;
         else if(tp == PO) Npo++;
      }
   }
   tbl = (int *) malloc(++ntbl * sizeof(int));

   fseek(fd, 0L, 0);
   i = 0;
   while(fgets(buf, MAXLINE, fd) != NULL) {
      if(sscanf(buf,"%d %d", &tp, &nd) == 2) tbl[nd] = i++;
   }
   allocate();

   fseek(fd, 0L, 0);
   while(fscanf(fd, "%d %d", &tp, &nd) != EOF) {
      np = &Node[tbl[nd]];
      np->num = nd;
      if(tp == PI) Pinput[ni++] = np;
      else if(tp == PO) Poutput[no++] = np;
      switch(tp) {
         case PI:
         case PO:
         case GATE:
            fscanf(fd, "%d %d %d", &np->type, &np->fout, &np->fin);
            break;
         
         case FB:
            np->fout = np->fin = 1;
            fscanf(fd, "%d", &np->type);
            break;

         default:
            printf("Unknown node type!\n");
            exit(-1);
         }
      np->unodes = (NSTRUC **) malloc(np->fin * sizeof(NSTRUC *));
      np->dnodes = (NSTRUC **) malloc(np->fout * sizeof(NSTRUC *));
      for(i = 0; i < np->fin; i++) {
         fscanf(fd, "%d", &nd);
         np->unodes[i] = &Node[tbl[nd]];
         }
      for(i = 0; i < np->fout; np->dnodes[i++] = NULL);
      }
   for(i = 0; i < Nnodes; i++) {
      for(j = 0; j < Node[i].fin; j++) {
         np = Node[i].unodes[j];
         k = 0;
         while(np->dnodes[k] != NULL) k++;
         np->dnodes[k] = &Node[i];
         }
      }
   fclose(fd);
   Gstate = CKTLD;
   printf("==> OK\n");
   return 1;
}

/*-----------------------------------------------------------------------
input: nothing
output: nothing
called by: main
description:
  The routine prints out the circuit description from previous READ command.
-----------------------------------------------------------------------*/
pc(cp)
char *cp;
{
   int i, j;
   NSTRUC *np;
   char *gname();
   
   printf(" Node   Type \t In    \t\t\t Levelization\t Out\n");
   printf("------ ------\t-------\t\t\t-------      \t-------\n");
   for(i = 0; i<Nnodes; i++) {
      np = &Node[i];
      printf("\t\t\t\t\t");
      printf("%d\t\t", np->level);
      for(j = 0; j<np->fout; j++) printf("%d ",np->dnodes[j]->num);
      //if (np->fout == 0) printf(" ");
      // printf("\there%d", np->indx);
      printf(" \r%5d  %s\t", np->num, gname(np->type));
      for(j = 0; j<np->fin; j++) printf("%d ",np->unodes[j]->num);
      printf("\n");
   }
   printf("\nPrimary inputs:  ");
   for(i = 0; i<Npi; i++) printf("%d ",Pinput[i]->num);
   printf("\n");
   printf("Primary outputs: ");
   for(i = 0; i<Npo; i++) printf("%d ",Poutput[i]->num);
   printf("\n\n");
   printf("Number of nodes = %d\n", Nnodes);
   printf("Number of primary inputs = %d\n", Npi);
   printf("Number of primary outputs = %d\n", Npo);
   return 1;
}

/*-----------------------------------------------------------------------
input: nothing
output: nothing
called by: main 
description:
  The routine prints ot help inormation for each command.
-----------------------------------------------------------------------*/
help()
{
   printf("READ filename - ");
   printf("read in circuit file and creat all data structures\n");
   printf("PC - ");
   printf("print circuit information\n");
   printf("LEV - ");
   printf("level circuit lines\n");
   printf("GFL - ");
   printf("Generate collapsed fault list\n");
   printf("PFS - ");
   printf("Parallel fault simulator\n"); 
   printf("HELP - ");
   printf("print this help information\n");
   printf("QUIT - ");
   printf("stop and exit\n");
   return 1;
}

/*-----------------------------------------------------------------------
input: nothing
output: nothing
called by: main 
description:
  Set Done to 1 which will terminates the program.
-----------------------------------------------------------------------*/
quit()
{
   Done = 1;
   return 1;
}

/*-----------------------------------------------------------------------
input: nothing
output: nothing
called by: cread
description:
  This routine clears the memory space occupied by the previous circuit
  before reading in new one. It frees up the dynamic arrays Node.unodes,
  Node.dnodes, Node.flist, Node, Pinput, Poutput, and Tap.
-----------------------------------------------------------------------*/
clear()
{
   int i;

   for(i = 0; i<Nnodes; i++) {
      free(Node[i].unodes);
      free(Node[i].dnodes);
   }
   free(Node);
   free(Pinput);
   free(Poutput);
   Gstate = EXEC;
}

/*-----------------------------------------------------------------------
input: nothing
output: nothing
called by: cread
description:
  This routine allocatess the memory space required by the circuit
  description data structure. It allocates the dynamic arrays Node,
  Node.flist, Node, Pinput, Poutput, and Tap. It also set the default
  tap selection and the fanin and fanout to 0.
-----------------------------------------------------------------------*/
allocate()
{
   int i;

   Node = (NSTRUC *) malloc(Nnodes * sizeof(NSTRUC));
   Pinput = (NSTRUC **) malloc(Npi * sizeof(NSTRUC *));
   Poutput = (NSTRUC **) malloc(Npo * sizeof(NSTRUC *));
   for(i = 0; i<Nnodes; i++) {
      Node[i].indx = i;
      Node[i].fin = Node[i].fout = 0;
   }
}

/*-----------------------------------------------------------------------
input: gate type
output: string of the gate type
called by: pc
description:
  The routine receive an integer gate type and return the gate type in
  character string.
-----------------------------------------------------------------------*/
char *gname(tp)
int tp;
{
   switch(tp) {
      case 0: return("PI");
      case 1: return("BRANCH");
      case 2: return("XOR");
      case 3: return("OR");
      case 4: return("NOR");
      case 5: return("NOT");
      case 6: return("NAND");
      case 7: return("AND");
   }
}

/*-----------------------------------------------------------------------
input: nothing
output: nothing
called by: main
description:
  Realize levelization of each circuit line after READ command.
-----------------------------------------------------------------------*/
lev()
{
   NSTRUC *np;
   char *gname();
   int i,j,k,m,maxlev;
   bool correct = 0;
   int sumnode = 0;

   Maxlevel = 0;

   while (1) {
       for(i = 0; i<Nnodes; i++) {
        np = &Node[i];
        if (np->islevel == 0) {
          if (np->type == 0) {
            np->level = 0;
            np->islevel = 1;
            sumnode++;
          }
          else if (np->type == 1) {
            if (np->unodes[0]->islevel == 1) {
              np->level = np->unodes[0]->level + 1;
              np->islevel = 1;
              sumnode++;
              if ((np->unodes[0]->level + 1) > Maxlevel){
                Maxlevel = np->unodes[0]->level + 1;
              }
            }         
          }
          else {
            maxlev = 0;
            correct = 1;
            for (j = 0; j<np->fin; j++) {
              if (np->unodes[j]->islevel == 1) {
                if (np->unodes[j]->level >= maxlev) {
                  maxlev = np->unodes[j]->level;
                }
              }
              else { 
                correct = 0; //some fins are not leveled.
                break;
              }             
            }
            if (correct) {
              np->level = maxlev + 1;
              np->islevel = 1;
              sumnode++;
              if (np->level > Maxlevel) {
                Maxlevel = np->level;
              }
            }
            //printf("maxlev = %d\n", maxlev);
          }
      }   
    }
    if (sumnode == Nnodes) break;
   }

   printf("==> OK\n");
}

/*-----------------------------------------------------------------------
input: nothing
output: nothing
called by: main
description:
  
-----------------------------------------------------------------------*/
preprocessor()
{
  FAULTLIST   *fp;
  NSTRUC      *np;
  int         i, Cpoints;

  Cpoints = 0;

  CompleteFL = (FAULTLIST *) malloc(Nnodes * sizeof(FAULTLIST));
  printf("Complete single stuck-at-fault list:\n");  
  for (i = 0; i < Nnodes; i++) {
    np = &Node[i];
    fp = &CompleteFL[i];
    fp->indx = i;
    if ((np->type == 0) | (np->type == 1)){
      Cpoints++;

    }
    printf("\tNode %d: (s_a_0, s_a_1)\t", i+1);
    fp->s_a_0 = 1;
    fp->s_a_1 = 1;
    if ((i+1)%2 == 0) printf("\n");
  }

  printf("\nCollapsed single stuck-at-fault list:\n");
  CollapsedFL = (FAULTLIST *) malloc(Cpoints * sizeof(FAULTLIST));




}


/*-----------------------------------------------------------------------
input: nothing
output: nothing
called by: main
description:
  
-----------------------------------------------------------------------*/
pfs()
{

}

/*========================= End of program ============================*/
fault_free_simulation(){
  int i,j,k;
  int *fault_free_output;       /*the array of the fault free simulation's output */

  fault_free_output = (int*)malloc(sizeof(int)*Npo);
  NSTRUC *np;

  for (i=0; i<Npi; i++){
    Pinput[i]->node_value = 0;        /*PI read the test pattern generated from ATPG???????*/
    printf("node:%d, indx:%d, type:%s, level:%d,node_value:%d\n",Pinput[i]->num, Pinput[i]->indx, gname(Pinput[i]->type), Pinput[i]->level, Pinput[i]->node_value);
  }

  for (i=1; i<=Maxlevel; i++){
    for (j=0; j<Nnodes; j++){
      np = &Node[j];
      if (np->level==i){
        switch(np->type){
          case 0:
              np->node_value = 1;
              printf("node:%d, indx:%d, type:%s, level:%d,node_value:%d\n",np->num, np->indx, gname(np->type), np->level, np->node_value);
              break;
          case 1://Branch
              np->node_value  = np->unodes[0]->node_value ;
              printf("node:%d, indx:%d, type:%s, level:%d,node_value:%d\n",np->num, np->indx, gname(np->type), np->level, np->node_value);
              break;
          case 2://XOR
              np->node_value  = 0;
               for (k=0; k<np->fin; k++){
                np->node_value  = np->unodes[k]->node_value  ^ np->node_value ;
              }
              printf("node:%d, indx:%d, type:%s, level:%d,node_value:%d\n",np->num, np->indx, gname(np->type), np->level, np->node_value);
              break;
          case 3://OR
              np->node_value = 0;
              for (k=0; k<np->fin; k++){
                if (np->unodes[k]->node_value ==1)
                  np->node_value  = 1;
              }
              printf("node:%d, indx:%d, type:%s, level:%d,node_value:%d\n",np->num, np->indx, gname(np->type), np->level, np->node_value);
              break;
          case 4://NOR
              np->node_value = 1;
              for (k=0; k<np->fin; k++){
                if (np->unodes[k]->node_value ==1)
                  np->node_value  = 0;
              }
              printf("node:%d, indx:%d, type:%s, level:%d,node_value:%d\n",np->num, np->indx, gname(np->type), np->level, np->node_value);
              break;
          case 5://NOT
              np->node_value  = !(np->unodes[0]->node_value);
              printf("node:%d, indx:%d, type:%s, level:%d,node_value:%d\n",np->num, np->indx, gname(np->type), np->level, np->node_value);
              break;
          case 6://NAND
              np->node_value = 0;
              for (k=0; k<np->fin; k++){
                if (np->unodes[k]->node_value ==0)
                  np->node_value  = 1;
              }
              printf("node:%d, indx:%d, type:%s, level:%d,node_value:%d\n",np->num, np->indx, gname(np->type), np->level, np->node_value);
              break;
          case 7://AND
              np->node_value = 1;
              for (k=0; k<np->fin; k++){
                if (np->unodes[k]->node_value ==0)
                  np->node_value  = 0;
              }
              printf("node:%d, indx:%d, type:%s, level:%d,node_value:%d\n",np->num, np->indx, gname(np->type), np->level, np->node_value);
              break;
          default:
              np->node_value = 2;
        }
      }
    }
  }

  for(i=0; i<Npo; i++){
    fault_free_output[i] = Poutput[i]->node_value;
    printf("\n Node:%d indx:%d type:%s leval:%d fault_free_output: %d\n", Poutput[i]->num, Poutput[i]->indx, gname(Poutput[i]->type), Poutput[i]->level, fault_free_output[i]);
  }

  return 1;
}



int* union_op(int*x, int*y){
  int i;
  int *z;
  z = malloc(sizeof(int)*Nnodes);
  for(i=0; i<Nnodes; i++){
    if (x[i]==y[i]){
      z[i] = x[i];
      printf("z:%d\n",z[i]);
    }
    else{
      if (x[i]==2)
        z[i] = y[i];
      else if (y[i]==2)
        z[i] = x[i];
      else if (x[i]==3)//non-exist case
        z[i] = 3;
      else if (y[i]==3)////non-exist case
        z[i] = 3;
      else 
        z[i] = 3;
      printf("z:%d\n",z[i]);
    }
  }
  /*free(x);
  free(y);
  free(z);*/
  return z;////?????????????????????
}

int* intersaction_op(int*x, int*y){
  int i;
  int *z;
  z = malloc(sizeof(int)*Nnodes);
  for(i=0; i<Nnodes; i++){
    if (x[i]==y[i]){
      z[i] = x[i];
      printf("z:%d\n",z[i]);
    }



    else{
      if((x[i]==3)&&(y[i]==1))
        z[i]= 1;
      if((x[i]==1)&&(y[i]==3))
        z[i]= 1;
      if((x[i]==3)&&(y[i]==0))
        z[i]= 0;
      if((x[i]==0)&&(y[i]==2))
        z[i]= 0;
      if((x[i]==2)&&(y[i]==1))
        z[i]= 2;
      if((x[i]==1)&&(y[i]==2))
        z[i]= 2;
      if((x[i]==2)&&(y[i]==0))
        z[i]= 2;
      if((x[i]==0)&&(y[i]==2))
        z[i]= 2;
      if((x[i]==2)&&(y[i]==3))
        z[i]= 2;
      if((x[i]==3)&&(y[i]==2))
        z[i]= 2;
      if((x[i]==2)&&(y[i]==3))
        z[i]= 2;
      if((x[i]==3)&&(y[i]==2))
        z[i]= 2;
    }
    printf("z:%d\n",z[i]);
   /*else{
      if (x[i]==3)//0:sa0, 1:sa1, 2:fault free, 3:either sa0 or sa1        
        z[i] = y[i];
       // printf("%d\n", z[i]);
      if (y[i]==3)
        z[i] = x[i];
      else 
        z[i] = 2;
      //printf("z:%d\n",z[i]);
    }
    printf("z:%d\n",z[i]);*/
  }
    printf("address of z = %d\n", &z);
    return z;
  }


int* minus_op(int*x, int*y){
  int i;
  int *z;
  z = malloc(sizeof(int)*Nnodes);
  for(i=0; i<Nnodes; i++){
    if (x[i]==y[i])
      z[i] = 2;
    else
      z[i] = x[i];
  }
  /*free(x);
  free(y);
  free(z);*/
  return z;////?????????????????????
}

int deductive_fault_simulation(){
  NSTRUC *np;
  int i,j,k;
  for (i = 0; i<Nnodes; i++){
      Node[i].L = malloc(sizeof(int)*Nnodes);
      for (j = 0; j < Nnodes; j++){
          Node[i].L[j] = 2;  // initialize each node 's fault list
      }
  }

  for (i = 0; i <= Maxlevel;i++){
    for (j=0;j<Nnodes;j++){
      np=&Node[j];
      /*printf("node:%d type:%s level :%d\n", np->num, gname(np->type),np->level);*/
      if(np->level == i){
        fault_list_propogate(&Node[j]);
      }
    }
  }

  printf("%d\n",count);
  for(i=0;i<Nnodes;i++){
    np=&Node[i];
    printf("node:%d type:%s level :%d\n", np->num, gname(np->type),np->level);
    for(j=0;j<Nnodes;j++){
      printf("%d ",Node[i].L[j]);
    }
    printf("\n");
    printf("\n");
  }

  return 1;
}

int fault_list_propogate(NSTRUC* np){
    int i, j, m;
    int *L1;
    int *L2;

        switch(np -> type){
            case 0:
                np->L[np->indx] = !(np->node_value);      
                break;
            case 1:
                for(i = 0; i<Nnodes; i++){
                    np->L[i]=np->unodes[0]->L[i]; 
                }
                np->L[np->indx] = !(np->node_value);
                break;
            case 2:
                break;
            case 3:
                L1 = malloc(sizeof(int)*Nnodes);
                for(i = 0; i<Nnodes; i++){
                    L1[i] = 3;
                }
                L2 = malloc(sizeof(int)*Nnodes);
                for(i = 0; i<Nnodes; i++){
                    L2[i] = 2;
                }

                if (np->node_value==0){  
                  for(i=0; i < np->fin; i++){
                    L2 = union_op(L2, np->unodes[i]->L);
                  }                                           //no input = control value
                  np->L = L2;
                }
                else {
                  for(i=0; i < np->fin; i++){
                    if(np->unodes[i]->node_value == 1){
                      for(m=0;m<Nnodes;m++){
                        printf("node:%d beforeIT_1:%d\n",np->num, L1[m]);
                      }
                      L1 = intersaction_op(L1, np->unodes[i]->L);
                    }
                    else{
                      L2 = union_op(L2, np->unodes[i]->L);
                    }
                    for(m=0;m<Nnodes;m++){
                      printf("node:%d L1:%d\n",np->num, L1[m]);
                      printf("node:%d L2:%d\n",np->num, L2[m]);     
                    }
                  } 
                  np->L = minus_op(L1, L2);  
                }

                np->L[np->indx] = !(np->node_value);
                break;   
            case 4: 
                L1 = malloc(sizeof(int)*Nnodes);
                for(i = 0; i<Nnodes; i++){
                    L1[i] = 3;
                }
                L2 = malloc(sizeof(int)*Nnodes);
                for(i = 0; i<Nnodes; i++){
                    L2[i] = 2;
                }

                if (np->node_value==1){  
                  for(i=0; i < np->fin; i++){
                    L2 = union_op(L2, np->unodes[i]->L);
                  }                                           //no input = control value
                  np->L = L2;
                }
                else {
                  for(i=0; i < np->fin; i++){
                    if(np->unodes[i]->node_value == 1){
                      L1 = intersaction_op(L1, np->unodes[i]->L);
                    }
                    else{
                      L2 = union_op(L2, np->unodes[i]->L);
                    }
                  }  
                  np->L = minus_op(L1, L2);
                }

                np->L[np->indx] = !(np->node_value);
                break;    
            case 5:
                np->L[np->indx] = !(np->node_value);
                break;
            case 6:                                          //NAND
                L1 = malloc(sizeof(int)*Nnodes);
                for(i = 0; i<Nnodes; i++){
                    L1[i] = 3;
                }
                L2 = malloc(sizeof(int)*Nnodes);
                for(i = 0; i<Nnodes; i++){
                    L2[i] = 2;
                }
                printf("node_value:%d\n",np->node_value);
                if (np->node_value==0){  
                  for(i=0; i < np->fin; i++){
                    L2 = union_op(L2, np->unodes[i]->L);
                  }                                           //no input = control value
                  np->L = L2;
                }
                else {
                  for(i=0; i < np->fin; i++){
                    if(np->unodes[i]->node_value == 0){
                      L1 = intersaction_op(L1, np->unodes[i]->L);
                      printf("address of L1 = %d\n", &L1);
                      for(m=0;m<Nnodes;m++){
                        printf("unodes%d L:%d\n", m, np->unodes[i]->L[m]);
                        printf("node:%d L1:%d\n",np->num, L1[m]);  
                    }
                    printf("\n");
                    }
                    else{
                      L2 = union_op(L2, np->unodes[i]->L);
                      for(m=0;m<Nnodes;m++){
                        printf("unodes%d L:%d\n", m, np->unodes[i]->L[m]);
                        printf("node:%d L2:%d\n",np->num, L2[m]);  
                    }
                    }
                    /*for(m=0;m<Nnodes;m++){
                      printf("node:%d L1:%d\n",np->num, L1[m]);
                      printf("node:%d L2:%d\n",np->num, L2[m]);     
                      }*/
                  } 
                    for(m=0;m<Nnodes;m++){
                      printf("finalL1 node:%d L1:%d\n",np->num, L1[m]);
                      printf("finalL2 node:%d L2:%d\n",np->num, L2[m]);     
                    }

                  np->L = minus_op(L1, L2);
                } 

                np->L[np->indx] = !(np->node_value);
                break;  
            case 7:
                L1 = malloc(sizeof(int)*Nnodes);
                for(i = 0; i<Nnodes; i++){
                    L1[i] = 3;
                }
                L2 = malloc(sizeof(int)*Nnodes);
                for(i = 0; i<Nnodes; i++){
                    L2[i] = 2;
                }

                if (np->node_value==1){  
                  for(i=0; i < np->fin; i++){
                    L2 = union_op(L2, np->unodes[i]->L);
                  }                                           //no input = control value
                  np->L = L2;
                }
                else {
                  for(i=0; i < np->fin; i++){
                    if(np->unodes[i]->node_value == 0){
                      L1 = intersaction_op(L1, np->unodes[i]->L);
                    }
                    else{
                      L2 = union_op(L2, np->unodes[i]->L);
                    }
                  } 
                  np->L = minus_op(L1, L2);
                }  
                np->L[np->indx] = !(np->node_value);
                break;  
        }
        
 return 1;
    }
  

