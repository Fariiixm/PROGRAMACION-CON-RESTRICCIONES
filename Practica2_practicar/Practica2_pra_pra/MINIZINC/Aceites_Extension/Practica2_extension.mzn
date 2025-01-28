%----------------------------------------------------------------------------
% Definición de los parámetros-----------------------------------------------
int: nMeses; % Número de meses
int: nAceiteVegetal; % Número de aceites vegetales
int: nAceiteNoVegetal; % Número de aceites no vegetales
int: nAceites = nAceiteVegetal + nAceiteNoVegetal; % Número total de aceites
int: VALOR; % Precio de venta del producto final
array[1..nAceites] of float: dureza; % Dureza de cada tipo de aceite
array[1..nMeses, 1..nAceites] of int: precios; % Precios de cada tipo de aceite para cada mes
int: MAXV; % Máximo de toneladas de aceites vegetales que se pueden refinar cada mes
int: MAXN; % Máximo de toneladas de aceites no vegetales que se pueden refinar cada mes
int: MCAP; % Capacidad de almacenamiento de la fábrica para cada tipo de aceite al inicio de cada mes
int: CA; % Costes de almacenamiento de cada tipo de aceite por tonelada y mes
float: MinD; % Dureza mínima del producto final
float: MaxD; % Dureza máxima del producto final
int: MinB; % Mínimo beneficio que tenemos que conseguir
array[1..nAceites] of int: inicial; % Cantidad inicial de cada tipo de aceite
int: PV; % Porcentaje de variación permitido respecto a lo que queda de cada producto en los almacenes al terminar los seis meses


int: K; % Número máximo de aceites que se pueden usar para hacer el producto
int: T; % Cantidad mínima de un aceite que se debe usar si se selecciona en un mes


int: MesesPerdida; % Número de meses consecutivos permitidos con pérdidas

%----------------------------------------------------------------------------
% Variables de decisión------------------------------------------------------

array[1..nMeses, 1..nAceites] of var 0..MCAP: compra; % Cantidad de cada tipo de aceite que se compra cada mes
array[1..nMeses, 1..nAceites] of var 0..MCAP: refinado; % Cantidad de cada tipo de aceite que se refina cada mes
array[1..nMeses] of var int: ventaMensual; % Cantidad de producto que se vende cada mes
array[1..nMeses, 1..nAceites] of var 0..MCAP: almacenado; % Cantidad de cada tipo de aceite que se almacena cada mes
array[1..nMeses] of var int: gananciaNetas; % Ganancias netas de cada mes

array[1..nMeses, 1..nAceites] of var 0..1: uso; % Indica si se usa un cierto aceite en un mes

%----------------------------------------------------------------------------
%Restricciones---------------------------------------------------------------

constraint assert(VALOR > 0, "El precio de venta debe ser > 0");
constraint assert(MCAP > 0, "La capacidad de almacenamiento debe ser > 0");
constraint forall(j in 1..nAceites) (assert(inicial[j] >= 0, "La cantidad inicial de cada tipo de aceite debe ser > 0"));
constraint forall(j in 1..nAceites) (assert(dureza[j] >= 0, "La dureza de cada tipo de aceite debe ser > 0"));

constraint forall(i in 1..nMeses, j in 1..nAceites) (
  if i > 1 then
    almacenado[i,j] <= almacenado[i-1,j] + compra[i,j] - refinado[i,j]
  else % el primer mes
    almacenado[i,j] <= inicial[j] + (compra[i,j] - refinado[i,j])
  endif
);

constraint forall(i in 1..nMeses, j in 1..nAceites)(almacenado[i,j]<=MCAP);

constraint forall(i in 1..nMeses)(
  sum(j in 1..nAceiteVegetal)(refinado[i, j]) <= MAXV /\
  sum(j in nAceiteNoVegetal..nAceites)(refinado[i, j]) <= MAXN
);

constraint forall(j in 1..nMeses)(
   ventaMensual[j] = sum(i in 1..nAceites) (refinado[j,i])
);

constraint forall(i in 1..nMeses, j in 1..nAceites)(
  if i > 1 then
    refinado[i,j] <= compra[i,j] + refinado[i-1,j]
  else
    refinado[i,j] <= compra[i,j]
  endif
);

constraint forall(i in 1..nMeses) (
  sum(j in 1..nAceites) (refinado[i,j] * dureza[j]) >= MinD * sum(j in 1..nAceites) (refinado[i,j])
);

constraint forall(i in 1..nMeses) (
  sum(j in 1..nAceites) (refinado[i,j] * dureza[j]) <= MaxD * sum(j in 1..nAceites) (refinado[i,j])
);

constraint forall(j in 1..nAceites) (
  abs(sum(i in 1..nMeses) (compra[i,j] - refinado[i,j]) - inicial[j]) <= PV * inicial[j]
);

constraint forall(i in 1..nMeses)(
  gananciaNetas[i] = (VALOR * ventaMensual[i]) - sum(j in 1..nAceites) (precios[i,j] * compra[i,j])
);

constraint forall(i in 3..nMeses) (
  if gananciaNetas[i-2] < 0 /\ gananciaNetas[i-1] < 0 then
    gananciaNetas[i] >= 0
  endif
);

var int: beneficio = sum(i in 1..nMeses, j in 1..nAceites) ((VALOR - precios[i,j]) * refinado[i,j]) - sum(i in 1..nMeses, j in 1..nAceites) (CA * compra[i,j]);


constraint beneficio >= MinB;


%------------------------------------------------------------------------
%Extension---------------------------------------------------------------

% Si se compra o se refina una cantidad positiva de un cierto aceite, entonces uso debe ser 1
constraint forall(i in 1..nMeses, j in 1..nAceites) (
  compra[i,j] + refinado[i,j] <= MCAP * uso[i,j]
);
% No se pueden usar más de K aceites para hacer el producto
constraint forall(i in 1..nMeses) (
  sum(j in 1..nAceites) (uso[i,j]) <= K
);

% Si se usa un cierto aceite en un mes, entonces se deben usar al menos T toneladas
constraint forall(i in 1..nMeses, j in 1..nAceites) (
  refinado[i,j] >= T * uso[i,j]
);

% Si se usan los aceites ANV 1 o ANV 2 en un cierto mes, entonces también se debe usar VEG 2
constraint forall(i in 1..nMeses) (
  ((uso[i,3] = 1) \/  (uso[i,4] = 1)) -> (uso[i,2] = 1)
);

%--------------------------------------------------

%solve maximize beneficio;
solve satisfy;

output [ "Beneficio: " ++ show(beneficio) ++ "\n" ] ++
[ "Compras de aceite:\n" ] ++ [ "Mes " ++ show(i) ++ ": " ++ show([compra[i,j] | j in 1..nAceites]) ++ "\n" | i in 1..nMeses ] ++
[ "\nCantidades de aceite refinado:\n" ] ++ [ "Mes " ++ show(i) ++ ": " ++ show([refinado[i,j] | j in 1..nAceites]) ++ "\n" | i in 1..nMeses ] ++
[ "\nVenta mensual de aceite:\n" ] ++ [ "Mes " ++ show(i) ++ ": " ++ show(ventaMensual[i]) ++ "\n" | i in 1..nMeses ] ++
[ "\nGanancias netas:\n" ] ++ [ "Mes " ++ show(i) ++ ": " ++ show(gananciaNetas[i]) ++ "\n" | i in 1..nMeses ]++
[ "\nCantidades de aceite almacenado:\n" ] ++ [ "Mes " ++ show(i) ++ ": " ++ show([almacenado[i,j] | j in 1..nAceites]) ++ "\n" | i in 1..nMeses ] ++
[ "\nUso de aceite:\n" ] ++ [ "Mes " ++ show(i) ++ ": " ++ show([uso[i,j] | j in 1..nAceites]) ++ "\n" | i in 1..nMeses ];

