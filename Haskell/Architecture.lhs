\documentclass{article}

\usepackage[utf8]{inputenc}
\usepackage[T1]{fontenc}

\usepackage{color}
\usepackage{graphicx}
\usepackage{wrapfig}

\usepackage{listings}
\lstloadlanguages{Haskell}
% auto-colorisation with listings, handy for known languages...
\lstdefinestyle{hsstyle}{
  basicstyle=\small,%\sffamily,
  language=haskell,
  emphstyle={\bf},
  commentstyle=\it,
  stringstyle=\mdseries\rmfamily,
  keywordstyle=\bfseries\rmfamily,
%
  escapeinside={*'}{'*},
  showspaces=false,
  showstringspaces=false,
  morecomment=[l]\%,
%
  stepnumber=1,
  numbers=left,
  numberstyle=\ttfamily\tiny\color[gray]{0.3},
  numbersep=5pt,
}
\lstnewenvironment{code}
   {\lstset{basicstyle=\scriptsize,style=hsstyle,frame=tlrb}}
   {}
\lstnewenvironment{mlcodesmall}
   {\lstset{basicstyle=\tiny,style=hsstyle,frame=tlrb}}
   {}
\lstset{style=hsstyle,keepspaces=true,breaklines=false}\newcommand{\cd}[1]{\lstinline$#1$}


%\author{Jost Berthold \and Martin Elsman}

\begin{document}

This is (tex-style) literate Haskell.
Enclose code like this:
\begin{code}
{-# LANGUAGE RankNTypes #-}
module Architecture
    where

import Data.List
import Data.Maybe
import System.Random
import Control.Monad.ST
\end{code}
and use suitable typesetting packages for code to enable latex.

\bigskip
\hrule
\bigskip

\paragraph*{The Big Picture:} to build software which enables a code-generation
and parallelism approach to financial computations,
using the \cd{Contracts.hs} module as a starting point.
%
While allowing for partial evaluation and parallelising compilation,
everything should be modular in the architecture.

\begin{center}
\includegraphics[width=\textwidth]{../doc/TheBigPicture}\\
\end{center}

\section*{Modules and key interface functions}

\paragraph*{Contracts Module:} The core multiparty contract.

\begin{code}
-- dummy definitions
type Contract = ()
type Date = Int

-- | an environment with phantom type 't' to constrain its domain
data Env t = Env ((String, Date) -> Double)

-- | Dependency type indexed with domain constraint
data Dep t = Dep [(String, Date)]

-- | generates the payoff function and constraints for the env.
genPayoff :: Contract -> forall t . ( Env t -> Double, Dep t)
genPayoff c = (undefined, undefined)
\end{code}

\paragraph*{Instruments Module:} many functions which create standard contracts
\begin{code}
-- ... 
\end{code}

\paragraph*{Model Module:}
producing a (stochastic) model from given dependencies.

\begin{code}
-- | this all should probably rather be called a stochastic process...
newtype Seed t = Seed Int
newtype MkEnv t = MkEnv (Seed t -> Env t)

-- | create a model from given dependencies, querying market data
model :: Dep t -> IO (MkEnv t)
model (Dep cs) 
    = do let os  = map fst cs
             ds  = nub (sort (map snd cs))
             cs' = [ (o,ds) | o <- os ]
         mds <- mapM getMarketData cs'
         let f s = Env $ \(x,d) -> fromJust (lookup x (zip os mds)) $ (s,d)
         return (MkEnv f)

getMarketData :: (String, [Date]) -> IO ((Seed t, Date) -> Double)
getMarketData _ = undefined
\end{code}

\paragraph*{Pricing Module:}
where it all fits together

\begin{code}
-- | Monte-Carlo price of a contract, given certain market data 

price :: Int -> Contract -> IO Double
price n c = do let (payoff, dep) = genPayoff c
               MkEnv m <- model dep
               let vs = map (\s -> payoff (m s)) seeds
               return (avg vs)
    where avg xs = sum xs / fromIntegral n
          seeds  = map Seed [1..n]
\end{code}

This is somewhat primitive... and these are not in fact seeds...

And: no discounting is included. Needs refinement.

\newpage

\section*{Another snippet of draft code\ldots}
This might end up in the future HQL library.

\paragraph*{Just some dummy definitions...}:
\begin{code}
type Cash = Double
data Swap = Swap
data SomeBond = SomeBond
\end{code}

\paragraph*{Instruments} are probably just derivatives.
Bonds are instruments, but a bond is also a type class in itself,
with different kinds of bond as its instances. A swap is an instrument.
\begin{code}
class Instrument i where
    someX :: Model m => m -> i -> Cash
    someX = undefined

class (Instrument b) => Bond b where
    something :: b -> Int
    something = undefined

instance Instrument SomeBond
instance Bond SomeBond 
\end{code}

\paragraph*{Models} are used to price instruments in a pricing engine.
\begin{code}
class Model m where
    someY :: Instrument i => i -> m -> Cash
    someY = undefined

data TermStructure = TermStructure (Double -> Double)
data OtherModel = Other (Int -> Double)

instance Model TermStructure
instance Model OtherModel
\end{code}

\paragraph*{Pricing engine} is where instruments and models are joined.
\begin{code}
class (Instrument i, Model p) => PricingEngine i p where
    pv :: i -> p -> Cash
    pv = undefined

instance PricingEngine SomeBond TermStructure
instance PricingEngine SomeBond OtherModel
instance PricingEngine Swap OtherModel
\end{code}

\end{document}
