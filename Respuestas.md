# Respuestas: Optimizando la maquina virtual#

## Ejercicio 6

Una solución podría ser cada vez que aparece un '_' no hacer el SHIFT luego de la compilación
de la definición de let, y en consecuencia no hacer un DROP. Una consideración a tener en cuenta
es que debemos restar en 1 los índices de las variables ligadas en el cuerpo.

## Ejercicio 7

Vamos a demostrar por induccion estructural sobre Term:

length (bcc (V _ (Bound n)))  = length([ACCESS,n]) = 2
length (bcc_O (V _ (Bound n)))  = length([ACCESS,n]) = 2

length (bcc (Const _ (CNat n))) = length ([CONST,n]) = 2
length (bcc_O (Const _ (CNat n))) = length ([CONST,n]) = 2

length (bcc (Lam _ _ _ t)) = length([FUNCTION,n]) + length(bcc t) + length([RETURN]) > HI
length([FUNCTION,n]) + length(bcc_O t) + length([RETURN]) = 
length([FUNCTION,n]) + length(bcc_O t) + 1 > Lema length(bcc_O t) + 1 > length(bct t)
length([FUNCTION,n]) + length(bct t) =
length([FUNCTION,n] ++ (bct t)) =
length(bcc_o (Lam _ _ _ t))



bcc (App _ t1 t2) = do
  t' <- bcc t1
  t'' <- bcc t2
  return $ t' ++ t'' ++ [CALL]
bcc (Print _ str t) = do
  t' <- bcc t
  return $ t' ++ PRINT:string2bc str ++ [NULL,PRINTN]
bcc (BinaryOp _ op t1 t2) = do
  t' <- bcc t1
  t'' <- bcc t2
  case op of
    Add -> return $ t' ++ t'' ++ [ADD]
    Sub -> return $ t' ++ t'' ++ [SUB]
bcc (Fix _ _ _ _ _ (Sc2 t)) = do
  t' <- bcc t
  return $ [FUNCTION,length t'] ++ t' ++ [RETURN,FIX]
bcc (IfZ _ c t1 t2) = do
  c' <- bcc c
  t' <- bcc t1
  t'' <- bcc t2
  return $ c' ++ [CJUMP,length t'+ 2] ++ t' ++ [JUMP,length t''] ++ t''
bcc (Let _ _ _ t1 (Sc1 t2)) = do
  t' <- bcc t1
  t'' <- bcc t2
* Casos base:

    + Sin optimizacion: C(n) = CONST n (con n natural)
        Con optimizacion: C(n) = CONST n
    + Sin optimizacion: C(v_i) = ACCESS v_i
        Con optimizacion: C(v_i) = ACCESS v_i
    Se puede ver que son iguales las compilaciones

* Casos inductivos:

    + Tenemos como hipotesis inductiva que , entonces
        Sin optimizacion: C(λt) = FUNCTION(C(t),RETURN) -> len(C(t)) + 2
        Con optimizacion: C(λt) = FUNCTION(T(t)) = FUNCTION(C(t),RETURN)

  return $ t' ++ [SHIFT] ++ t'' ++ [DROP]

## Ejercicio 8

En el caso de la Macchina sin optimizar no se usa memoria constante ya que 
en la funcion recursiva cuando se llama a CALL guarda la direccion de retorno del llamante,
lo cual al ser una funcion que se llama a si misma infinitamente, cada instruccion CALL agrega
la direccion de retorno al stack. En el caso de la Macchina optimizada, al leer la instruccion
TAILCALL recupera el entorno de la funcion recursiva y su codigo, pero no guarda la direccion de retorno
ya que se va a usar la que se guardo anteriormente. Esto implica que el stack no se va a ver incrementado,
por lo que en este caso el uso de memoria es constante.