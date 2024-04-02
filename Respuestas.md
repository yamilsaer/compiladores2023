# Respuestas: Maquina virtual#
## Inciso d

Macchina:
real    9m9,553s
user    8m42,981s
sys     0m40,384s

C nativo:
real    0m0,411s
user    0m0,406s
sys     0m0,006s

# Respuestas: Optimizando la maquina virtual#

## Ejercicio 6

Una solución podría ser cada vez que aparece un '_' no hacer el SHIFT luego de la compilación
de la definición de let, y en consecuencia no hacer un DROP. Una consideración a tener en cuenta
es que debemos restar en 1 los índices de las variables ligadas en el cuerpo.

## Ejercicio 8

En el caso de la Macchina sin optimizar no se usa memoria constante ya que 
en la funcion recursiva cuando se llama a CALL guarda la direccion de retorno del llamante,
lo cual al ser una funcion que se llama a si misma infinitamente, cada instruccion CALL agrega
la direccion de retorno al stack. En el caso de la Macchina optimizada, al leer la instruccion
TAILCALL recupera el entorno de la funcion recursiva y su codigo, pero no guarda la direccion de retorno
ya que se va a usar la que se guardo anteriormente. Esto implica que el stack no se va a ver incrementado,
por lo que en este caso el uso de memoria es constante.