module Derive.Kit

import Language.Reflection.Elab
import Language.Reflection.Utils

%default total

||| Generate a name that looks like some previous name, for ease of
||| debugging code generators.
nameFrom : TTName -> Elab TTName
nameFrom (UN x) = gensym $ if length x == 0 || ("_" `isPrefixOf` x)
                             then "x"
                             else x
nameFrom (NS n ns) = flip NS ns <$> nameFrom n
nameFrom (MN x n) = gensym $ if length n == 0 || ("_" `isPrefixOf` n)
                               then "n"
                               else n
nameFrom (SN x) = gensym "SN"
nameFrom NErased = gensym "wasErased"
