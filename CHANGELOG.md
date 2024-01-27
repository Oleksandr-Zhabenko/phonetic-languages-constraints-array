# Revision history for phonetic-languages-constraints-array

## 0.1.0.0 -- 2020-12-31

* First version. Released to the world.

## 0.1.1.0 -- 2022-03-24

* First version revised A. Updated the dependency boundaries to support the latest GHC and Cabal versions. Added some experimental functions that 
are not further used.

## 0.1.2.0 -- 2022-04-25

* First version revised B. Added the new constraint P functionality.

## 0.2.0.0 -- 2023-01-31

* Second version. Switched to NoImplicitPrelude extension. Changed the names of the modules. Updated the dependencies boundaries.

## 0.3.0.0 -- 2023-05-15

* Third version. Added new types of constraints based on the signed and unsigned distance(s)
between two or three elements (encoded with the capital letters V, W, H, R).

## 0.4.0.0 -- 2023-05-15

* Fourth version. Added a new type of constraint based on both signed and unsigned distances
between three elements (encoded with M). Some documentation improvements.

## 0.4.1.0 -- 2023-05-16

* Fourth version revised. Changed the number of parameters for the new constructors added. Added
isM function to the export from the module.

## 0.5.0.0 -- 2023-05-17

* Fifth version. Changed representation in the EncodedCnstr data type. Removed the readMaybeEC
function. Reduced code duplication. Switched the way of counting -- moved all to one natural base
of 1 and more.

## 0.6.0.0 -- 2023-05-22 

* Sixth version. Added new functions to the Phladiprelio.Constraints module for negated constraints. 
Added some boolean algebra interpeter for constraints to Phladiprelio.ConstraintsEncoded module. 
Added README.md file and devotion of the project to Foundation Gastrostars. 

## 0.6.1.0 -- 2023-05-23

* Sixth version revised A. Added new function filterGeneralConv to Phladiprelio.ConstraintsEncoded 
module. Added also validOrdStr to the export list in the module. Some minor documentation
improvements. 

## 0.6.1.1 -- 2023-05-23

* Sixth version revised B. Some minor code improvements.

## 0.6.2.0 -- 2023-05-25

* Sixth version revised C. Fixed the issues with precedence of the (&&) and (||) logical operators. 
Now it should behave as usual and as is defined in Haskell98 and Haskell2010. 

## 0.7.0.0 -- 2023-05-31

* Seventh version. Added new constraints encoding to the Phladiprelio.ContstraintsEncoded module 
(N, D, I). Some documentation improvements.

## 0.7.0.1 -- 2023-05-31

* Seventh version revised A. Some minor documentation improvements.

## 0.7.1.0 -- 2023-06-01

* Seventh version revised B. Fixed some issues with incorrect False validation for algebraic constraints
handling that lead to no constraints at all for applications and in the oneChange function with 
incorrect foldr function definition. Now the algebraic constraints functionality should work better 
(hopefully, as expected).

## 0.7.2.0 -- 2023-06-02

* Seventh version revised C. Fixed issue with the shadowing of the variable in the lambda function
in the oneChange function definition that leads to incorrect behaviour of the parentheses handling.
Some minor documentation and code improvements.

## 0.7.3.0 -- 2023-06-06

* Seventh version revised D. Added new constraint type U for five elements. Switched to bit
  algorithms in some functions (mostly for testing and more readable code). 

## 0.8.0.0 -- 2024-01-27

* Eighth version. Updated the dependencies and switched to monoid-insertleft instead of subG. Added specializing and inlining for some functions to improve performance. Some documentation improvements.

