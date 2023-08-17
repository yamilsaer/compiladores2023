# Compiladores
Código para la materia Compiladores 2023 de [LCC](https://dcc.fceia.unr.edu.ar), [FCEIA](https://www.fceia.unr.edu.ar), [UNR](https://www.unr.edu.ar).

Este es el código a partir del cual los estudiantes empiezan a desarrollar un compilador.

Para correr el proyecto basta con ejecutar:

```code
cabal run
```

Las opciones soportadas por el intérprete pueden verse utilizando el comando `:help` :
```code
FD4> :help
Lista de comandos:  Cualquier comando puede ser abreviado a :c donde
c es el primer caracter del nombre completo.

<expr>                  evaluar la expresión
let <var> = <expr>      definir una variable
:browse                 Ver los nombres en scope
:load <file>            Cargar un programa desde un archivo
:print <exp>            Imprime un término y sus ASTs sin evaluarlo
:reload                 Vuelve a cargar el último archivo cargado
:type <exp>             Chequea el tipo de una expresión
:quit, :Q               Salir del intérprete
:help, :?               Mostrar esta lista de comandos
```
