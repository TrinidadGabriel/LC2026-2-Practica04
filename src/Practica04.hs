module Practica04 where

--Sintaxis de la logica proposicional
data Prop = Var String | Cons Bool | Not Prop
            | And Prop Prop | Or Prop Prop
            | Impl Prop Prop | Syss Prop Prop
            deriving (Eq)

instance Show Prop where 
                    show (Cons True) = "⊤"
                    show (Cons False) = "⊥"
                    show (Var p) = p
                    show (Not p) = "¬" ++ show p
                    show (Or p q) = "(" ++ show p ++ " ∨ " ++ show q ++ ")"
                    show (And p q) = "(" ++ show p ++ " ∧ " ++ show q ++ ")"
                    show (Impl p q) = "(" ++ show p ++ " → " ++ show q ++ ")"
                    show (Syss p q) = "(" ++ show p ++ " ↔ " ++ show q ++ ")"

type Literal = Prop
type Clausula = [Literal]

p, q, r, s, t, u :: Prop
p = Var "p"
q = Var "q"
r = Var "r"
s = Var "s"
t = Var "t"
u = Var "u"

--Definicion de los tipos para la practica
type Interpretacion = [( String , Bool ) ]
type Estado = ( Interpretacion , [Clausula])
data ArbolDPLL = Node Estado ArbolDPLL | Branch Estado ArbolDPLL ArbolDPLL | Void deriving Show

--IMPLEMENTACION PARTE 1
--Ejercicio 1
conflict :: Estado -> Bool
conflict (_, []) = False                                                       --Revisa si la lista de clausulas esta vacia
conflict (interp, (c:cs)) = if null c then True else conflict (interp, cs)     --Abre la lista y revisa que las clausulas no sean listas vacias

--Ejercicio 2
success :: Estado -> Bool
success (_, clausulas) = null clausulas                                         --Revisa que las clausulas esten vacias

--Ejercicio 3
unit :: Estado -> Estado
unit (interp, []) = (interp, [])                                                --El caso base: si ya no hay clausulas que revisar, regresamos el estado tal como esta.
unit (interp, ([Var x] : cs)) = ((x, True) : interp, cs)                        --Si la primera clausula de la lista tiene un elemento,entonces extrae la x, la coloca como True en la interpretación, y devuélveme el resto de las cláusulas (cs).
unit (interp, ([Not (Var x)] : cs)) = ((x, False) : interp, cs)                 --Si la primera clausula de la lista tiene un elemento,entonces extrae la x, la coloca como False en la interpretación, y devuélveme el resto de las cláusulas (cs).
unit (interp, (c : cs)) = (i', c : cs')                                         --Si la primera clausula no tiene un elemento, continua con las demas clausulas
  where
    (i', cs') = unit (interp, cs)

--Ejercicio 4
elim :: Estado -> Estado
elim (interp, clausulas) = (interp, filtrarClausulas interp clausulas)
  where
    filtrarClausulas _ [] = []                                                  --Caso base. Si la lista de clausulas esta vacaa, devuelve una lista vacía.
    filtrarClausulas int (c:cs) =                                               --Toma la lista y saca la primera cláusula. El resto de las cláusulas se quedan en cs.
        if clausulaEsVerdadera int c                                            --Revisa si la clausula es verdadera 
        then filtrarClausulas int cs                                            --Si es verdadera, no la agregamos al resultado y simplemente seguimos filtrando el resto
        else c : filtrarClausulas int cs                                        --Si no es verdadera, entonces se queda. La pegamos al inicio con c : y seguimos filtrando el resto.


    clausulaEsVerdadera _ [] = False                                            --Si ya revisamos todos los literales de la cláusula y llegamos a la lista vacía [], significa que no encontramos nada útil. La cláusula entera es falsa.
    clausulaEsVerdadera int (l:ls) =                                            --Toma la cláusula y saca su primer literal (l). Los demás literales quedan en ls.
        if literalEsVerdadero int l                                             --Revisa si la literal es verdadera
        then True                                                               --Si el literal es verdadero, toda la cláusula ya es verdadera. Nos detenemos ahí y devolvemos True. No necesitamos revisar los demás.
        else clausulaEsVerdadera int ls                                         --Si el literal es falso o no lo conocemos, no podemos afirmar nada. Hacemos la llamada recursiva para revisar el siguiente literal en la lista (ls).

    -- Verificación de la literal
    literalEsVerdadero [] _ = False                                             --Caso base: Si recorrimos toda la interpretación y llegamos al final ([]), significa que nuestro literal no esta en la lista. Devolvemos False.
    
    literalEsVerdadero ((v, b):is) (Var x) =                                    --Tomamos el primer par de la interpretación (su nombre y su valor). Esta regla solo se activa si el literal que estamos buscando es una variable normal (Var x).
        if x == v && b == True                                                  --Comparamos: Si la variable que buscamos ya esta y además, si su valor en el es True
        then True                                                               --Si ambas cosas coinciden, el literal es verdadero.
        else literalEsVerdadero is (Var x)
        
    literalEsVerdadero ((v, b):is) (Not (Var x)) =                              --Es parecida a la anterior pero con la variable negada
        if x == v && b == False 
        then True 
        else literalEsVerdadero is (Not (Var x))
        
    literalEsVerdadero (_:is) l = literalEsVerdadero is l                       --Si la función recibe algo que no coincide con las reglas de arriba, ignora ese paso (_) y simplemente avanza al siguiente elemento de la interpretación.

--Ejercicio 5
red :: Estado -> Estado
red (interp, clausulas) = (interp, reducirClausulas interp clausulas)           ----Tomamos el estado y lo separamos. La interpretación se queda igual en el resultado, pero la lista de clausulas se la enviamos a nuestra primera función auxiliar: reducirClausulas.

  where
    reducirClausulas _ [] = []                                                  --Caso base. Si ya no quedan cláusulas por revisar en la lista, regresamos una lista vacía [].
    reducirClausulas int (c:cs) = reducirUna int c : reducirClausulas int cs    --Saca la primera cláusula de la lista. Llama a reducirUna para encoger esa cláusula c. Y hace una llamada recursiva para seguir encogiendo el resto de las cláusulas. Finalmente, pega la cláusula encogida con el resto.

    -- Recorre una sola cláusula eliminando los literales falsos                
    reducirUna _ [] = []                                                        --Caso base. Si ya revisamos todos los literales de esta cláusula, devolvemos una lista vacía.                                  
    reducirUna int (l:ls) =                                                     --Toma el primer literal de la cláusula. El resto de los literales se quedan en ls.
        if literalEsFalso int l                                                 --Verificacia si la literal es falsa                                   
        then reducirUna int ls                                                  --Si es falso, la regla dice que no sirve. Así que seguimos revisando el resto de los literales (ls).
        else l : reducirUna int ls                                              --Si no es falso (puede ser verdadero o simplemente no lo conocemos todavía), entonces se salva. Lo pegamos al inicio del resultado con l :  y seguimos revisando el resto.

    -- buscar si la literal es falso
    literalEsFalso [] _ = False                                                 --Caso base: Si recorrimos toda la interpretación y no encontramos a la variable, asumimos que no es falsa (devolvemos False).
    
    literalEsFalso ((v, b):is) (Var x) =                                        
        if x == v && b == False                                                 --Compara con el primer elemento de la interpretación (v, b).
        then True                                                               --Si ambas cosas coinciden, el literal es verdadero.
        else literalEsFalso is (Var x)
        
    literalEsFalso ((v, b):is) (Not (Var x)) =                                  ----Es parecida a la anterior pero con la variable negada
        if x == v && b == True 
        then True 
        else literalEsFalso is (Not (Var x))
        
    literalEsFalso (_:is) l = literalEsFalso is l                               --Si hay un dato que no encaja en las dos reglas de arriba, lo ignóra y avanza al siguiente elemento.


--Ejercicio 6
sep :: Literal -> Estado -> (Estado, Estado)
sep (Var x) (interp, clausulas) =                                               --Esta regla se activa si nos pasan un literal positiva. También desarmamos el Estado actual en su interp y sus clausulas.
    ( ((x, True) : interp, clausulas), ((x, False) : interp, clausulas) )       --El lado izquierdo: Tomamos nuestra 'interp' y le agregamos la nueva suposición (x, True). Las cláusulas se quedan exactamente igual.
                                                                                --El lado derecho: Tomamos la misma interp y ahora le agregamos la suposición opuesta (x, False). Las cláusulas también se quedan igual.
    
sep (Not (Var x)) (interp, clausulas) = 
    ( ((x, True) : interp, clausulas), ((x, False) : interp, clausulas) )       --Es casi lo mismo que arriba pero con la variable negada

sep _ estado = (estado, estado)                                                 --Si recibe algo que no es ni Var ni Not Var, simplemente toma el estado en el que estábamos y devuelve ese mismo estado duplicado (estado, estado). 


--IMPLEMENTACION PARTE 2


--Ejercicio 1
heuristicsLiteral :: [Clausula] -> Literal
heuristicsLiteral cs = buscarMax (contarLiterales (aplanar cs))                 --Primero toma las cláusulas cs y las aplana. Luego cuenta cuántas veces aparece cada literal en esa lista plana. Finalmente, busca el máximo de esos conteos.

  where
    -- Convierte la lista de listas en una sola lista larga
    aplanar [] = []                                                             --Si la lista principal está vacía, devuelve vacío.
    aplanar (c:resto) = c ++ (aplanar resto)                                    --Si tiene cláusulas, toma la primera cláusula c y la concatena con el resultado de aplanar el resto.

    -- Cuenta cuántas veces aparece cada literal
    contarLiterales [] = []
    contarLiterales (l:ls) = (l, 1 + contar l ls): contarLiterales (quitar l ls)    --Toma el primer literal de la lista (l). Usa la función contar para ver cuántas veces más aparece ese mismo literal en el resto de la lista, y le suma 1 (por el que tenemos).
    
    contar _ [] = 0
    contar x (y:ys) = if x == y then 1 + contar x ys else contar x ys           --Recorre la lista. Si el elemento y es igual al que buscamos x, suma 1. Si no, sigue buscando.
    
    quitar _ [] = []
    quitar x (y:ys) = if x == y then quitar x ys else y : quitar x ys           --Recorre la lista. Si encuentra a nuestro elemento x, lo ignora (lo elimina). Si es distinto, lo conserva y sigue avanzando.

    -- Busca el que tenga el número mayor en la lista contada
    buscarMax [] = Var "error"                                                  --Un caso de error por si le pasamos una lista vacía.
    buscarMax [(l, _)] = l                                                      --Caso base. Si en la lista ya solo queda uno. Devolvemos su letra l.
    buscarMax ((l1, n1):(l2, n2):resto) =                                       --Toma a las dos primeros literales de la lista. l1 con su puntuación n1, y l2 con su puntuación n2. El resto espera su turno.
        if n1 >= n2                                                             --Si la primera literal tiene más o los mismas repeticiones que la segunda literal , la segunda literal queda eliminado. 
        then buscarMax ((l1, n1):resto)                                         --Hacemos recursión volviendo a meter a la primera literal a comparar con el resto.
        else buscarMax ((l2, n2):resto)                                         --Hacemos recursión volviendo a meter a la segunda lieteral a comparar con el resto. Y la primera es eliminada

--EJERCICIO 2
dpll :: [Clausula] -> Interpretacion
dpll c = solve (Node ([], c) Void)                                              --Arrancamos nuestra función interna solve. Le damos el punto de partida: un Node cuyo estado inicial tiene un diccionario vacío [] y las cláusulas c originales.
  where
    -- Caso 1: Si llegamos a un hueco en el árbol, regresamos vacío
    solve Void = []                                                             --Si solve llega a un Void, significa que este camino no sirvió. Regresa una lista vacía [], que es nuestra señal de "fracaso" en esta ruta.
    
    -- Caso 2: Procesar un Nodo
    solve (Node (i,cs) arbol) =                                                    --Si estamos en un Node, extraemos su estado est.
        if success (i,cs)                                                       --Primero pregunta si fue exitoso. 
        then i                                                                  --Si es así, extraemos la interpretación final y terminamos.
        else if conflict (i,cs)                                                 --Si no, preguntamos si hubo un error y calusula vacia (conflict est). 
        then []                                                                 --Si es así, devolvemos [] indicando que este camino fracasó.
        else procesarSimplificacion (i,cs) (red (elim (unit (i,cs))))                 --Si no fracaso pero tampoco fue exito. Tomamos el estado: primero unit, luego elim y luego red. El resultado de esto junto con el Estado Viejo (est) se lo pasamos a procesarSimplificacion.
    
    -- Caso 3: Procesar una Ramificación (Branch)
    solve (Branch est izq der) =                                                --Si estamos en un Branch, tenemos un camino izquierdo izq y uno derecho der.
        if solve izq == []                                                      --Mandamos a resolver el camino izquierdo (solve izq). Si el resultado es vacío (fracasó)
        then solve der                                                          --Entonces nos pasamos con el camino derecho (solve der).
        else solve izq                                                          --Pero si el izquierdo no está vacío, nos quedamos con esa respuesta.
    
    -- Esta función decide si ramificar o seguir simplificando
    procesarSimplificacion estViejo (iNuevo, csNuevo) =                                  --Recibe cómo estaba el problema antes de red (elim (unit...)) y cómo quedó después.
        if estViejo == (iNuevo, csNuevo)                                        --Si son iguales, significa que nuestras reglas lógicas se atascaron. No pudieron deducir nada nuevo.
        then bifurcar (iNuevo, csNuevo) (heuristicsLiteral csNuevo)             --Llamamos a bifurcar, pasándole la variable más repetida usando nuestra función heuristicsLiteral.
        else solve (Node (iNuevo, csNuevo) Void)                                --Si no son iguales, significa que las reglas lógicas sí lograron encoger el problema. Así que volvemos a llamar a solve creando un nuevo Node con el problema encogido para que vuelva a dar otra vuelta.
        
    
    -- Construye el branch
    bifurcar est l = crearRamas est (sep l est)                                 --bifurcar llama a sep pasándole la variable l para crear los dos estados paralelos. 
    
    crearRamas est (eIzq, eDer) = 
        solve (Branch est (Node eIzq Void) (Node eDer Void))                    --recibe la tupla y la parte automáticamente en eIzq y eDer, usándolos para construir el Branch con sus dos hijos.

--EXTRA
dpll2 :: Prop -> Interpretacion
dpll2 = undefined
