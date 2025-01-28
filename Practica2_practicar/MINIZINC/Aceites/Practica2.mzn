%----------------------------------------------------------------------------
% Definición de los parámetros-----------------------------------------------

int: nMeses;
int: nAceiteVegetal;
int: nAceiteNoVegetal;
int: nAceites = nAceiteVegetal + nAceiteNoVegetal;
int: VALOR;
array[1..nAceites] of float: dureza;
array[1..nMeses, 1..nAceites] of int: precios;
int: MAXV;
int: MAXN;
int: MCAP;
int: CA;
float: MinD;
float: MaxD;
int: MinB;
array[1..nAceites] of int: inicial;
int: PV;

int: MesesPerdida;

%----------------------------------------------------------------------------
% Variables de decisión------------------------------------------------------


array[1..nMeses, 1..nAceites] of var 0..MCAP: compra;
array[1..nMeses, 1..nAceites] of var 0..MCAP: refinado;
array[1..nMeses] of var int: ventaMensual;
array[1..nMeses, 1..nAceites] of var 0..MCAP: almacenado;
array[1..nMeses] of var int: gananciaNetas;


%----------------------------------------------------------------------------
%Restricciones---------------------------------------------------------------

constraint assert(VALOR > 0, "El precio de venta debe ser > 0");
constraint assert(MCAP > 0, "La capacidad de almacenamiento debe ser > 0");
constraint forall(j in 1..nAceites) (assert(inicial[j] >= 0, "La cantidad inicial de cada tipo de aceite debe ser > 0"));
constraint forall(j in 1..nAceites) (assert(dureza[j] >= 0, "La dureza de cada tipo de aceite debe ser > 0"));



%almacenamiento inicial y actualizacion
constraint forall(i in 1..nMeses, j in 1..nAceites) (
  if i > 1 then
    almacenado[i,j] <= almacenado[i-1,j] + compra[i,j] - refinado[i,j]
  else % el primer mes
    almacenado[i,j] <= inicial[j] + (compra[i,j] - refinado[i,j])
  endif
);

%limitar almacen
constraint forall(i in 1..nMeses, j in 1..nAceites)(almacenado[i,j]<=MCAP);

%limitar cuanto refinamos
constraint forall(i in 1..nMeses)(
  %sum(j in 1..nAceites)(compra[i,j]) <= MCAP /\
  sum(j in 1..nAceiteVegetal)(refinado[i, j]) <= MAXV /\
  sum(j in nAceiteNoVegetal..nAceites)(refinado[i, j]) <= MAXN
);

%suma de todo el aceite refinado(vendido) 
constraint forall(j in 1..nMeses)(
   ventaMensual[j] = sum(i in 1..nAceites) (refinado[j,i])
);

%iniciar refinado, y actualizacion por acumulacion. No exceder compra
constraint forall(i in 1..nMeses, j in 1..nAceites)(
  if i > 1 then
    refinado[i,j] <= compra[i,j] + refinado[i-1,j]
  else
    refinado[i,j] <= compra[i,j]
  endif
);

%refinado no exceda min dureza
constraint forall(i in 1..nMeses) (
  sum(j in 1..nAceites) (refinado[i,j] * dureza[j]) >= MinD * sum(j in 1..nAceites) (refinado[i,j])
);

% no exceda max dureza
constraint forall(i in 1..nMeses) (
  sum(j in 1..nAceites) (refinado[i,j] * dureza[j]) <= MaxD * sum(j in 1..nAceites) (refinado[i,j])
);



% Restricción de variación de almacenamiento
constraint forall(j in 1..nAceites) (
  abs(sum(i in 1..nMeses) (compra[i,j] - refinado[i,j]) - inicial[j]) <= PV * inicial[j]
);

% Calculo de las ganancias netas
constraint forall(i in 1..nMeses)(
  gananciaNetas[i] = (VALOR * ventaMensual[i]) - sum(j in 1..nAceites) (precios[i,j] * compra[i,j])
);

% Restricción de perdidas consecutivas
constraint forall(i in 3..nMeses) (
  if gananciaNetas[i-2] < 0 /\ gananciaNetas[i-1] < 0 then
    gananciaNetas[i] >= 0
  endif
);

%beneficio total obtenido a lo largo del año
var int: beneficio = sum(i in 1..nMeses, j in 1..nAceites) ((VALOR - precios[i,j]) * refinado[i,j]) - sum(i in 1..nMeses, j in 1..nAceites) (CA * compra[i,j]);

constraint beneficio >= MinB;

%maximizar beneficio
solve maximize beneficio;

% Salida de datos
output [ "Beneficio: " ++ show(beneficio) ++ "\n" ] ++
[ "Compras de aceite:\n" ] ++ [ "Mes " ++ show(i) ++ ": " ++ show([compra[i,j] | j in 1..nAceites]) ++ "\n" | i in 1..nMeses ] ++
[ "\nCantidades de aceite refinado:\n" ] ++ [ "Mes " ++ show(i) ++ ": " ++ show([refinado[i,j] | j in 1..nAceites]) ++ "\n" | i in 1..nMeses] ++
[ "\nVenta mensual de aceite:\n" ] ++ [ "Mes " ++ show(i) ++ ": " ++ show(ventaMensual[i]) ++ "\n" | i in 1..nMeses ] ++
[ "\nGanancias netas:\n" ] ++ [ "Mes " ++ show(i) ++ ": " ++ show(gananciaNetas[i]) ++ "\n" | i in 1..nMeses ]++
[ "\nCantidades de aceite almacenado:\n" ] ++ [ "Mes " ++ show(i) ++ ": " ++ show([almacenado[i,j] | j in 1..nAceites]) ++ "\n" | i in 1..nMeses ];
