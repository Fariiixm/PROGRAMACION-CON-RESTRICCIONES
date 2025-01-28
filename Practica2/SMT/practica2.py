#!/usr/bin/python3
from z3 import *
import sys

# nMeses
# nAceites
# valor 
# dureza
# precios
# MAXV
# MAXN
# MCAP
# CA
# MinD
# MaxD
# MinB
# inicial
# PV
# MesesPerdida




valor = int(input())
MAXV = int(input())
MAXN = int(input())
MCAP = int(input())
CA = int(input())
MinD = float(input())
MaxD = float(input())
MinB = int(input())
PV = int(input())
nMeses = int(input())
MesesPerdida = int(input())
nAceiteVegetal = int(input())
nAceiteNoVegetal = int(input())

nAceites = nAceiteVegetal + nAceiteNoVegetal

# Leer los valores iniciales
inputParam = input().split()
inicial = []
for i in range(nAceites):
    inicial.append(int(inputParam[i]))

# Leer los valores de dureza
inputParam = input().split()
dureza = []
for i in range(nAceites):#len(inputParam)):
    dureza.append(float(inputParam[i]))

# matriz de precios
precios = []
for _ in range(nMeses):
    matriz = input().split()
    precios_fila = [int(j) for j in matriz]
    precios.append(precios_fila)

def comprasMatrix(i,j):
    return Int("compra_%d_%d" % (i, j))

def refinadoMatrix(i,j):
    return Int("refinado_%d_%d" % (i, j))
def almacenadoMatrix(i,j):
    return Int("almacenado_%d_%d" % (i, j))

def usadoMatrix(i,j):
    return Int("usado_%d_%d" % (i,j))


################################
# generamos un fichero smtlib2
################################
s = Optimize()
#s = SolverFor("QF_LIA")# para imprimir s.to_smt2() al final del codigo
# s = Solver()


compra = [[0] * nAceites for _ in range(nMeses)]
refinado = [[0] * nAceites for _ in range(nMeses)]
almacenado = [[0] * nAceites for _ in range(nMeses)]


for i in range(nMeses):
    for j in range(nAceites):
        compra[i][j] = comprasMatrix(i,j)
        s.add(compra[i][j] >= 0)
        s.add(compra[i][j] <= MCAP)

        refinado[i][j] = refinadoMatrix(i,j)
        s.add(refinado[i][j] >= 0)
        s.add(refinado[i][j] <= MCAP)

        almacenado[i][j] = almacenadoMatrix(i,j)
        s.add(almacenado[i][j] >= 0)
        s.add(almacenado[i][j] <= MCAP)
#---------------------------------------------------------------------------------------------------------------------
#constraint forall(i in 1..nMeses, j in 1..nAceites) (
#  if i > 1 then
#    almacenado[i,j] <= almacenado[i-1,j] + compra[i,j] - refinado[i,j]
#  else % el primer mes
#    almacenado[i,j] <= inicial[j] + compra[i,j] - refinado[i,j]
#  endif
#);
for i in range(nMeses):
    for j in range(nAceites):
        if i > 0:
            s.add(almacenado[i][j] == almacenado[i-1][j] + compra[i][j] - refinado[i][j])
        else:
            s.add(almacenado[i][j] == inicial[j] + compra[i][j] - refinado[i][j])


#constraint forall(i in 1..nMeses)(
#  %sum(j in 1..nAceites)(compra[i,j]) <= MCAP /\
#  sum(j in 1..nAceiteVegetal)(refinado[i, j]) <= MAXV /\
#  sum(j in nAceiteNoVegetal..nAceites)(refinado[i, j]) <= MAXN
#);

for i in range(nMeses):
    #s.add(Sum([compra[i][j] for j in range(nAceites)]) <= MCAP)
    s.add(Sum([refinado[i][j] for j in range(nAceiteVegetal)]) <= MAXV)
    s.add(Sum([refinado[i][j] for j in range(nAceiteNoVegetal, nAceites)]) <= MAXN)
#end

for i in range(nMeses):
    for j in range(nAceites):
        if i > 0:
            s.add(almacenado[i][j] <= almacenado[i-1][j] + compra[i][j] - refinado[i][j])
        else:
            s.add(almacenado[i][j] <= inicial[j] + compra[i][j] - refinado[i][j])
almacenado

#constraint forall(j in 1..nMeses)(
#   ventaMensual[j] = sum(i in 1..nAceites) (refinado[j,i])
#);
#ventaMensual = [0 for _ in range(nMeses)]
ventaMensual = []
for i in range(nMeses):
    ventaMensual.append(Sum([refinado[i][j] for j in range(nAceites)]))
    s.add(ventaMensual[i] == Sum([refinado[i][j] for j in range(nAceites)]))


#constraint forall(i in 1..nMeses, j in 1..nAceites)(
#  if i > 1 then
#    refinado[i,j] <= compra[i,j] + refinado[i-1,j]
#  else
#    refinado[i,j] <= compra[i,j]
#  endif
#);

for i in range(nMeses):
    for j in range(nAceites):
        if i > 0:
            s.add(refinado[i][j] <= compra[i][j] + refinado[i-1][j])
        else:
            s.add(refinado[i][j] <= compra[i][j])
refinado

#constraint forall(i in 1..nMeses) (
#  sum(j in 1..nAceites) (refinado[i,j] * dureza[j]) >= MinD * sum(j in 1..nAceites) (refinado[i,j])
#);
for i in range(nMeses):
    s.add(
        Sum([refinado[i][j] * dureza[j] for j in range(nAceites)]) >= MinD * Sum([refinado[i][j] for j in range(nAceites)]))
#end

#constraint forall(j in 1..nAceites) (
#  abs(sum(i in 1..nMeses) (compra[i,j] - refinado[i,j]) - inicial[j]) <= PV * inicial[j]
#);

#for j in range(nAceites):
#   s.add(abs(Sum([compra[i][j] - refinado[i][j] for i in range(nMeses)]) - inicial[j]) <= PV * inicial[j])
#end
for j in range(nAceites):
    s.add(If(Sum([compra[i][j] - refinado[i][j] for i in range(nMeses)]) - inicial[j] >= 0, 
             Sum([compra[i][j] - refinado[i][j] for i in range(nMeses)]) - inicial[j], 
            -(Sum([compra[i][j] - refinado[i][j] for i in range(nMeses)]) - inicial[j])) <= PV * inicial[j])


#constraint forall(i in 1..nMeses)(
#  gananciaNetas[i] = (VALOR * ventaMensual[i]) - sum(j in 1..nAceites) (precios[i,j] * compra[i,j])
#);   
gananciaNetas = []
for i in range(nMeses):
    gananciaNetas.append((valor * ventaMensual[i]) - Sum([precios[i][j] * compra[i][j] for j in range(nAceites)]))
    s.add(gananciaNetas[i] == (valor * ventaMensual[i]) - Sum([precios[i][j] * compra[i][j] for j in range(nAceites)]))
#end

#constraint forall(i in 3..nMeses) (
#  if gananciaNetas[i-2] < 0 /\ gananciaNetas[i-1] < 0 then
#    gananciaNetas[i] >= 0
#  endif
#);
for i in range(2, nMeses):
    s.add(If(And(gananciaNetas[i-2] < 0, gananciaNetas[i-1] < 0), gananciaNetas[i] >= 0, gananciaNetas[i] == gananciaNetas[i]))



#var int: beneficio = sum(i in 1..nMeses, j in 1..nAceites) ((VALOR - precios[i,j]) * refinado[i,j]) - sum(i in 1..nMeses, j in 1..nAceites) (CA * compra[i,j]);
beneficio = Sum([Sum([(valor - precios[i][j]) * refinado[i][j] for j in range(nAceites)]) - Sum([CA * compra[i][j] for j in range(nAceites)]) for i in range(nMeses)])

s.add(beneficio >= MinB)

####################################################################################################################
#--------------------------Obtimizar la cantidad de aceites utilizados en cada mes----------------------------------
####################################################################################################################


# Minimizar el número de aceites usados cada mes
usado = [[usadoMatrix(i,j) for i in range(nAceites)] for j in range(nMeses)]

# Luego, en tus restricciones, puedes agregar lo siguiente:
for i in range(nMeses):
    for j in range(nAceites):
        s.add(usado[i][j] == If(refinado[i][j] > 0, 1, 0))# if refinado[m][a] > 0 then 1 else 0)

sumCantidadAceites = [Sum([usado[i][j] for j in range(nAceites)]) for i in range(nMeses)]
s.minimize(Sum(sumCantidadAceites)) # minimizar la cantidad de aceites usados en cada mes

#tarda un poco en dar la solucion


####################################################################################################################
#--------------------------Solucion--------------------------------------------------------------------------------
####################################################################################################################

if s.check() == sat:
    m = s.model()
    print("beneficio: ", m.eval(beneficio), "\n")
    print("\n\ncompra: \n")
    for i in compra:
        print([m.eval(j) for j in i])
    print("\n\nrefinado:\n")
    for i in refinado:
        print([m.eval(j) for j in i])
    print("\n\nalmacenado:\n")
    for i in almacenado:
        print([m.eval(j) for j in i])
    print("\n\nventaMensual: \n")
    for i in ventaMensual:
        print(m.eval(i))
    print("\n\ngananciaNetas: \n")
    for i in gananciaNetas:
        print(m.eval(i))
    print("\n\nusado: \n")
    for i in usado:
        print([m.eval(j) for j in i])

        
else:
    print("No se encontro una solucion")
    
    
#print("\n\nsmt2: \n")
#print(s.to_smt2())

exit(0)

##############################
