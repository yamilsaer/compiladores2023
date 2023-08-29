# Compiladores
Código para la materia Compiladores 2023 de [LCC](https://dcc.fceia.unr.edu.ar), [FCEIA](https://www.fceia.unr.edu.ar), [UNR](https://www.unr.edu.ar).

Este es el código a partir del cual los estudiantes empiezan a desarrollar un compilador.

## Intérprete FD4

Para correr el intérprete basta con ejecutar:

```code
cabal run
```

Las opciones soportadas por el intérprete de FD4 pueden verse utilizando el comando `:help` :
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
## Entorno interactivo con GHCi

También pueden cargar un módulo específico del proyecto en el entorno interactivo GHCi:

```code
cabal exec ghci -- -isrc src/Parse.hs
```
La bandera `-isrc` es necesaria para indicarle a GHCi que los archivos que importa el módulo que
estamos cargando deben ser buscados dentro de la carpeta `src/`.

Alternativamente, pueden inicializar GHCi:
```code
cabal exec ghci
```

Y luego cargar el archivo deseado desde allí:

```code
ghci> :cd src/
ghci> :load Parse.hs
[1 of 3] Compiling Common           ( Common.hs, interpreted )
[2 of 3] Compiling Lang             ( Lang.hs, interpreted )
[3 of 3] Compiling Parse            ( Parse.hs, interpreted )
Ok, three modules loaded.
```
Notar que de esta forma también es necesario corregir el PATH de los archivos para no tener
problemas con las dependencias.