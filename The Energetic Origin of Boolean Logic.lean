{\rtf1\ansi\ansicpg936\cocoartf2822
\cocoatextscaling0\cocoaplatform0{\fonttbl\f0\fnil\fcharset0 Menlo-Regular;\f1\fswiss\fcharset0 Helvetica;}
{\colortbl;\red255\green255\blue255;\red0\green0\blue255;\red255\green255\blue255;\red0\green0\blue0;
\red15\green112\blue1;\red19\green118\blue70;\red107\green0\blue1;}
{\*\expandedcolortbl;;\cssrgb\c0\c0\c100000;\cssrgb\c100000\c100000\c100000;\cssrgb\c0\c0\c0;
\cssrgb\c0\c50196\c0;\cssrgb\c3529\c52549\c34510;\cssrgb\c50196\c0\c0;}
\paperw11900\paperh16840\margl1440\margr1440\vieww11520\viewh8400\viewkind0
\deftab720
\pard\pardeftab720\partightenfactor0

\f0\fs24 \cf2 \cb3 \expnd0\expndtw0\kerning0
\outl0\strokewidth0 \strokec2 import\cf0 \strokec4  Mathlib\cb1 \
\cf2 \cb3 \strokec2 noncomputable\cf0 \strokec4  \cf2 \strokec2 section\cf0 \cb1 \strokec4 \
\cf2 \cb3 \strokec2 open\cf0 \strokec4  Real\cb1 \
\
\cf2 \cb3 \strokec2 namespace\cf0 \strokec4  Residual\cb1 \
\cf2 \cb3 \strokec2 set_option\cf0 \strokec4  autoImplicit \cf2 \strokec2 false\cf0 \cb1 \strokec4 \
\cf2 \cb3 \strokec2 set_option\cf0 \strokec4  linter.unusedVariables \cf2 \strokec2 false\cf0 \cb1 \strokec4 \
\cf5 \cb3 \strokec5 -- \uc0\u22914 \u26524 \u19981 \u24819 \u30475 \u26576 \u20123 \u25552 \u31034 \u65292 \u20063 \u21487 \u20197 \u21152 \u65306 \cf0 \cb1 \strokec4 \
\cf5 \cb3 \strokec5 -- set_option linter.unnecessarySimpa false\cf0 \cb1 \strokec4 \
\cf5 \cb3 \strokec5 -- set_option linter.unnecessarySeqFocus false\cf0 \cb1 \strokec4 \
\
\cf5 \cb3 \strokec5 /-\cf0 \cb1 \strokec4 \
\cf5 \cb3 \strokec5   Params: (\uc0\u955 , \u954 ) parameters of the analytic energy law\cf0 \cb1 \strokec4 \
\cf5 \cb3 \strokec5     E(x,y) = (\uc0\u955 (x+y) + \u954 xy)\'b2\cf0 \cb1 \strokec4 \
\cf5 \cb3 \strokec5 -/\cf0 \cb1 \strokec4 \
\cf2 \cb3 \strokec2 structure\cf0 \strokec4  Params \cf2 \strokec2 where\cf0 \cb1 \strokec4 \
\cb3   lam : \uc0\u8477 \cb1 \
\cb3   kap : \uc0\u8477 \cb1 \
\cf2 \cb3 \strokec2 deriving\cf0 \strokec4  DecidableEq\cb1 \
\
\cf5 \cb3 \strokec5 ------------------------------------------------------------\cf0 \cb1 \strokec4 \
\cf5 \cb3 \strokec5 -- THEOREM 1 : Analytic energy & Hessian symmetry\cf0 \cb1 \strokec4 \
\cf5 \cb3 \strokec5 ------------------------------------------------------------\cf0 \cb1 \strokec4 \
\
\cf5 \cb3 \strokec5 /-- Continuous energy on \uc0\u8477 \'b2: E(x,y) = (\u955 (x+y) + \u954 xy)\'b2. -/\cf0 \cb1 \strokec4 \
\cf2 \cb3 \strokec2 def\cf0 \strokec4  E (p : Params) (x y : \uc0\u8477 ) : \u8477  :=\cb1 \
\cb3   \cf2 \strokec2 let\cf0 \strokec4  g := p.lam*(x + y) + p.kap*x*y\cb1 \
\cb3   g * g\cb1 \
\
\cf5 \cb3 \strokec5 /-- \uc0\u8706 E/\u8706 x : symbolic derivative (no calculus library). -/\cf0 \cb1 \strokec4 \
\cf2 \cb3 \strokec2 def\cf0 \strokec4  dE_dx (p : Params) (x y : \uc0\u8477 ) : \u8477  :=\cb1 \
\cb3   \cf2 \strokec2 let\cf0 \strokec4  g := p.lam*(x + y) + p.kap*x*y\cb1 \
\cb3   \cf2 \strokec2 let\cf0 \strokec4  L := p.lam + p.kap*y\cb1 \
\cb3   \cf6 \strokec6 2\cf0 \strokec4  * g * L\cb1 \
\
\cf5 \cb3 \strokec5 /-- \uc0\u8706 E/\u8706 y : symbolic derivative. -/\cf0 \cb1 \strokec4 \
\cf2 \cb3 \strokec2 def\cf0 \strokec4  dE_dy (p : Params) (x y : \uc0\u8477 ) : \u8477  :=\cb1 \
\cb3   \cf2 \strokec2 let\cf0 \strokec4  g := p.lam*(x + y) + p.kap*x*y\cb1 \
\cb3   \cf2 \strokec2 let\cf0 \strokec4  L := p.lam + p.kap*x\cb1 \
\cb3   \cf6 \strokec6 2\cf0 \strokec4  * g * L\cb1 \
\
\cf5 \cb3 \strokec5 /-- \uc0\u8706 \'b2E/\u8706 x\'b2 : second derivative in x, 2\'b7(\u955 +\u954 y)\'b2. -/\cf0 \cb1 \strokec4 \
\cf2 \cb3 \strokec2 def\cf0 \strokec4  d2E_dx2 (p : Params) (x y : \uc0\u8477 ) : \u8477  :=\cb1 \
\cb3   \cf6 \strokec6 2\cf0 \strokec4  * (p.lam + p.kap*y)^\cf6 \strokec6 2\cf0 \cb1 \strokec4 \
\
\cf5 \cb3 \strokec5 /-- \uc0\u8706 \'b2E/\u8706 y\'b2 : second derivative in y, 2\'b7(\u955 +\u954 x)\'b2. -/\cf0 \cb1 \strokec4 \
\cf2 \cb3 \strokec2 def\cf0 \strokec4  d2E_dy2 (p : Params) (x y : \uc0\u8477 ) : \u8477  :=\cb1 \
\cb3   \cf6 \strokec6 2\cf0 \strokec4  * (p.lam + p.kap*x)^\cf6 \strokec6 2\cf0 \cb1 \strokec4 \
\
\cf5 \cb3 \strokec5 /-- \uc0\u8706 \'b2E/(\u8706 x\u8706 y) : mixed second derivative. -/\cf0 \cb1 \strokec4 \
\cf2 \cb3 \strokec2 def\cf0 \strokec4  d2E_dxdy (p : Params) (x y : \uc0\u8477 ) : \u8477  :=\cb1 \
\cb3   \cf2 \strokec2 let\cf0 \strokec4  g  := p.lam*(x + y) + p.kap*x*y\cb1 \
\cb3   \cf2 \strokec2 let\cf0 \strokec4  Lx := p.lam + p.kap*y\cb1 \
\cb3   \cf2 \strokec2 let\cf0 \strokec4  Ly := p.lam + p.kap*x\cb1 \
\cb3   \cf6 \strokec6 2\cf0 \strokec4  * (Lx * Ly + p.kap*g)\cb1 \
\
\cf5 \cb3 \strokec5 /-- Hessian of E at (x,y) as a 2\'d72 matrix. -/\cf0 \cb1 \strokec4 \
\cf2 \cb3 \strokec2 def\cf0 \strokec4  Hessian (p : Params) (x y : \uc0\u8477 ) :\cb1 \
\cb3   Matrix (Fin \cf6 \strokec6 2\cf0 \strokec4 ) (Fin \cf6 \strokec6 2\cf0 \strokec4 ) \uc0\u8477  :=\cb1 \
\cb3   \cf2 \strokec2 fun\cf0 \strokec4  i j =>\cb1 \
\cb3     \cf2 \strokec2 match\cf0 \strokec4  i.val, j.val \cf2 \strokec2 with\cf0 \cb1 \strokec4 \
\cb3     | \cf6 \strokec6 0\cf0 \strokec4 ,\cf6 \strokec6 0\cf0 \strokec4  => d2E_dx2 p x y\cb1 \
\cb3     | \cf6 \strokec6 0\cf0 \strokec4 ,\cf6 \strokec6 1\cf0 \strokec4  => d2E_dxdy p x y\cb1 \
\cb3     | \cf6 \strokec6 1\cf0 \strokec4 ,\cf6 \strokec6 0\cf0 \strokec4  => d2E_dxdy p x y\cb1 \
\cb3     | \cf6 \strokec6 1\cf0 \strokec4 ,\cf6 \strokec6 1\cf0 \strokec4  => d2E_dy2 p x y\cb1 \
\cb3     | _,_ => \cf6 \strokec6 0\cf0 \strokec4    \cf5 \strokec5 -- \uc0\u19981 \u20250 \u34987 \u30495 \u30340 \u29992 \u21040 \u65292 \u21482 \u26159 \u20445 \u35777  total\cf0 \cb1 \strokec4 \
\
\cf5 \cb3 \strokec5 /-- THEOREM 1 (formal):\cf0 \cb1 \strokec4 \
\cf5 \cb3 \strokec5     For all parameters (\uc0\u955 ,\u954 ) and all (x,y), the Hessian of E is symmetric. -/\cf0 \cb1 \strokec4 \
\cf2 \cb3 \strokec2 lemma\cf0 \strokec4  Hessian_symm (p : Params) (x y : \uc0\u8477 ) :\cb1 \
\cb3   Matrix.transpose (Hessian p x y) = Hessian p x y := \cf2 \strokec2 by\cf0 \cb1 \strokec4 \
\cb3   funext i j\cb1 \
\cb3   cases' i using Fin.cases <;> cases' j using Fin.cases <;>\cb1 \
\cb3   simp [Hessian, Matrix.transpose]\cb1 \
\
\cf5 \cb3 \strokec5 ------------------------------------------------------------\cf0 \cb1 \strokec4 \
\cf5 \cb3 \strokec5 -- \uc0\u22522 \u30784 \u65306 \u20108 \u38454 \u23548 \u30340 \u38750 \u36127 \u24615  / \u27491 \u24615 \u65288 Theorem 4 \u35201 \u29992 \u65289 \cf0 \cb1 \strokec4 \
\cf5 \cb3 \strokec5 ------------------------------------------------------------\cf0 \cb1 \strokec4 \
\
\cf5 \cb3 \strokec5 /-- \uc0\u8706 \'b2E/\u8706 x\'b2 \u8805  0 for all (x,y). -/\cf0 \cb1 \strokec4 \
\cf2 \cb3 \strokec2 lemma\cf0 \strokec4  d2E_dx2_nonneg (p : Params) (x y : \uc0\u8477 ) :\cb1 \
\cb3   \cf6 \strokec6 0\cf0 \strokec4  \uc0\u8804  d2E_dx2 p x y := \cf2 \strokec2 by\cf0 \cb1 \strokec4 \
\cb3   unfold d2E_dx2\cb1 \
\cb3   \cf2 \strokec2 have\cf0 \strokec4  h2 : \cf6 \strokec6 0\cf0 \strokec4  \uc0\u8804  (\cf6 \strokec6 2\cf0 \strokec4  : \uc0\u8477 ) := \cf2 \strokec2 by\cf0 \strokec4  norm_num\cb1 \
\cb3   \cf2 \strokec2 have\cf0 \strokec4  hL : \cf6 \strokec6 0\cf0 \strokec4  \uc0\u8804  (p.lam + p.kap*y)^\cf6 \strokec6 2\cf0 \strokec4  := \cf2 \strokec2 by\cf0 \cb1 \strokec4 \
\cb3     \cf2 \strokec2 have\cf0 \strokec4  := sq_nonneg (p.lam + p.kap*y)\cb1 \
\cb3     simpa [pow_two] using this\cb1 \
\cb3   exact mul_nonneg h2 hL\cb1 \
\
\cf5 \cb3 \strokec5 /-- \uc0\u8706 \'b2E/\u8706 y\'b2 \u8805  0 for all (x,y). -/\cf0 \cb1 \strokec4 \
\cf2 \cb3 \strokec2 lemma\cf0 \strokec4  d2E_dy2_nonneg (p : Params) (x y : \uc0\u8477 ) :\cb1 \
\cb3   \cf6 \strokec6 0\cf0 \strokec4  \uc0\u8804  d2E_dy2 p x y := \cf2 \strokec2 by\cf0 \cb1 \strokec4 \
\cb3   unfold d2E_dy2\cb1 \
\cb3   \cf2 \strokec2 have\cf0 \strokec4  h2 : \cf6 \strokec6 0\cf0 \strokec4  \uc0\u8804  (\cf6 \strokec6 2\cf0 \strokec4  : \uc0\u8477 ) := \cf2 \strokec2 by\cf0 \strokec4  norm_num\cb1 \
\cb3   \cf2 \strokec2 have\cf0 \strokec4  hL : \cf6 \strokec6 0\cf0 \strokec4  \uc0\u8804  (p.lam + p.kap*x)^\cf6 \strokec6 2\cf0 \strokec4  := \cf2 \strokec2 by\cf0 \cb1 \strokec4 \
\cb3     \cf2 \strokec2 have\cf0 \strokec4  := sq_nonneg (p.lam + p.kap*x)\cb1 \
\cb3     simpa [pow_two] using this\cb1 \
\cb3   exact mul_nonneg h2 hL\cb1 \
\
\cf5 \cb3 \strokec5 /-- If \uc0\u955 +\u954 y \u8800  0, then \u8706 \'b2E/\u8706 x\'b2 > 0. -/\cf0 \cb1 \strokec4 \
\cf2 \cb3 \strokec2 lemma\cf0 \strokec4  d2E_dx2_pos (p : Params) (x y : \uc0\u8477 )\cb1 \
\cb3   (hL : p.lam + p.kap*y \uc0\u8800  \cf6 \strokec6 0\cf0 \strokec4 ) :\cb1 \
\cb3   \cf6 \strokec6 0\cf0 \strokec4  < d2E_dx2 p x y := \cf2 \strokec2 by\cf0 \cb1 \strokec4 \
\cb3   unfold d2E_dx2\cb1 \
\cb3   \cf2 \strokec2 have\cf0 \strokec4  h2 : \cf6 \strokec6 0\cf0 \strokec4  < (\cf6 \strokec6 2\cf0 \strokec4  : \uc0\u8477 ) := \cf2 \strokec2 by\cf0 \strokec4  norm_num\cb1 \
\cb3   \cf2 \strokec2 have\cf0 \strokec4  hL2 : \cf6 \strokec6 0\cf0 \strokec4  < (p.lam + p.kap*y)^\cf6 \strokec6 2\cf0 \strokec4  := \cf2 \strokec2 by\cf0 \cb1 \strokec4 \
\cb3     \cf2 \strokec2 have\cf0 \strokec4  h : p.lam + p.kap*y \uc0\u8800  \cf6 \strokec6 0\cf0 \strokec4  := hL\cb1 \
\cb3     \cf5 \strokec5 -- 4.24 \uc0\u29256 \u26412 \u65306 sq_pos_of_ne_zero \u21482 \u25509 \u25910 \u36825 \u20010 \u35777 \u26126 \cf0 \cb1 \strokec4 \
\cb3     simpa [pow_two] using (sq_pos_of_ne_zero h)\cb1 \
\cb3   exact mul_pos h2 hL2\cb1 \
\
\cf5 \cb3 \strokec5 /-- If \uc0\u955 +\u954 x \u8800  0, then \u8706 \'b2E/\u8706 y\'b2 > 0. -/\cf0 \cb1 \strokec4 \
\cf2 \cb3 \strokec2 lemma\cf0 \strokec4  d2E_dy2_pos (p : Params) (x y : \uc0\u8477 )\cb1 \
\cb3   (hL : p.lam + p.kap*x \uc0\u8800  \cf6 \strokec6 0\cf0 \strokec4 ) :\cb1 \
\cb3   \cf6 \strokec6 0\cf0 \strokec4  < d2E_dy2 p x y := \cf2 \strokec2 by\cf0 \cb1 \strokec4 \
\cb3   unfold d2E_dy2\cb1 \
\cb3   \cf2 \strokec2 have\cf0 \strokec4  h2 : \cf6 \strokec6 0\cf0 \strokec4  < (\cf6 \strokec6 2\cf0 \strokec4  : \uc0\u8477 ) := \cf2 \strokec2 by\cf0 \strokec4  norm_num\cb1 \
\cb3   \cf2 \strokec2 have\cf0 \strokec4  hL2 : \cf6 \strokec6 0\cf0 \strokec4  < (p.lam + p.kap*x)^\cf6 \strokec6 2\cf0 \strokec4  := \cf2 \strokec2 by\cf0 \cb1 \strokec4 \
\cb3     \cf2 \strokec2 have\cf0 \strokec4  h : p.lam + p.kap*x \uc0\u8800  \cf6 \strokec6 0\cf0 \strokec4  := hL\cb1 \
\cb3     simpa [pow_two] using (sq_pos_of_ne_zero h)\cb1 \
\cb3   exact mul_pos h2 hL2\cb1 \
\
\cf5 \cb3 \strokec5 ------------------------------------------------------------\cf0 \cb1 \strokec4 \
\cf5 \cb3 \strokec5 -- THEOREM 2 : XOR discrete minimum on \{0,1\}\'b2\cf0 \cb1 \strokec4 \
\cf5 \cb3 \strokec5 ------------------------------------------------------------\cf0 \cb1 \strokec4 \
\
\cf5 \cb3 \strokec5 /-- Discrete energy on Boolean inputs. -/\cf0 \cb1 \strokec4 \
\cf2 \cb3 \strokec2 def\cf0 \strokec4  Eb (p : Params) (a b : Bool) : \uc0\u8477  :=\cb1 \
\cb3   E p (\cf2 \strokec2 if\cf0 \strokec4  a \cf2 \strokec2 then\cf0 \strokec4  \cf6 \strokec6 1\cf0 \strokec4  \cf2 \strokec2 else\cf0 \strokec4  \cf6 \strokec6 0\cf0 \strokec4 ) (\cf2 \strokec2 if\cf0 \strokec4  b \cf2 \strokec2 then\cf0 \strokec4  \cf6 \strokec6 1\cf0 \strokec4  \cf2 \strokec2 else\cf0 \strokec4  \cf6 \strokec6 0\cf0 \strokec4 )\cb1 \
\
\cf5 \cb3 \strokec5 /-- XOR-region: \uc0\u20004 \u20010  XOR \u35282  (1,0) \u21644  (0,1) \u31561 \u33021 \u37327 \u12289 \cf0 \cb1 \strokec4 \
\cf5 \cb3 \strokec5     \uc0\u19988 \u20005 \u26684 \u20302 \u20110 \u21478 \u22806 \u20004 \u20010 \u35282  (0,0)\u12289 (1,1). -/\cf0 \cb1 \strokec4 \
\cf2 \cb3 \strokec2 def\cf0 \strokec4  isXORregion (p : Params) : \cf2 \strokec2 Prop\cf0 \strokec4  :=\cb1 \
\cb3   Eb p \cf2 \strokec2 true\cf0 \strokec4  \cf2 \strokec2 false\cf0 \strokec4  = Eb p \cf2 \strokec2 false\cf0 \strokec4  \cf2 \strokec2 true\cf0 \strokec4  \uc0\u8743 \cb1 \
\cb3   Eb p \cf2 \strokec2 true\cf0 \strokec4  \cf2 \strokec2 false\cf0 \strokec4  < Eb p \cf2 \strokec2 false\cf0 \strokec4  \cf2 \strokec2 false\cf0 \strokec4  \uc0\u8743 \cb1 \
\cb3   Eb p \cf2 \strokec2 true\cf0 \strokec4  \cf2 \strokec2 false\cf0 \strokec4  < Eb p \cf2 \strokec2 true\cf0 \strokec4  \cf2 \strokec2 true\cf0 \cb1 \strokec4 \
\
\cf5 \cb3 \strokec5 /-- THEOREM 2 (formal):\cf0 \cb1 \strokec4 \
\cf5 \cb3 \strokec5     If \cf7 \strokec7 `p`\cf5 \strokec5  is in the XOR-region, then for all Boolean (a,b),\cf0 \cb1 \strokec4 \
\cf5 \cb3 \strokec5     Eb(a,b) \uc0\u8805  Eb(1,0), and Eb(1,0) = Eb(0,1).\cf0 \cb1 \strokec4 \
\
\cf5 \cb3 \strokec5     \uc0\u21363 \u65306 \u22312  \{0,1\}\'b2 \u19978 \u65292 \u21807 \u19968 \u30340 \u26497 \u23567 \u28857 \u38598 \u21512 \u26159  \{(1,0),(0,1)\}. -/\cf0 \cb1 \strokec4 \
\cf2 \cb3 \strokec2 theorem\cf0 \strokec4  XOR_unique_min (p : Params)\cb1 \
\cb3   (h : isXORregion p) :\cb1 \
\cb3   (\uc0\u8704  a b, Eb p a b \u8805  Eb p \cf2 \strokec2 true\cf0 \strokec4  \cf2 \strokec2 false\cf0 \strokec4 ) \uc0\u8743 \cb1 \
\cb3   Eb p \cf2 \strokec2 true\cf0 \strokec4  \cf2 \strokec2 false\cf0 \strokec4  = Eb p \cf2 \strokec2 false\cf0 \strokec4  \cf2 \strokec2 true\cf0 \strokec4  := \cf2 \strokec2 by\cf0 \cb1 \strokec4 \
\cb3   rcases h \cf2 \strokec2 with\cf0 \strokec4  \uc0\u10216 hSym, hLT00, hLT11\u10217 \cb1 \
\cb3   refine And.intro ?min ?eq\cb1 \
\cb3   \'b7 intro a b\cb1 \
\cb3     cases a <;> cases b\cb1 \
\cb3     \'b7 \cf5 \strokec5 -- (false,false)\cf0 \cb1 \strokec4 \
\cb3       exact le_of_lt hLT00\cb1 \
\cb3     \'b7 \cf5 \strokec5 -- (false,true) \uc0\u35201 \u35777 \u26126  Eb 0 1 \u8805  Eb 1 0\cf0 \cb1 \strokec4 \
\cb3       \cf2 \strokec2 have\cf0 \strokec4  : Eb p \cf2 \strokec2 false\cf0 \strokec4  \cf2 \strokec2 true\cf0 \strokec4  = Eb p \cf2 \strokec2 true\cf0 \strokec4  \cf2 \strokec2 false\cf0 \strokec4  := \cf2 \strokec2 by\cf0 \cb1 \strokec4 \
\cb3         simpa [eq_comm] using hSym\cb1 \
\cb3       \cf5 \strokec5 -- \uc0\u36716 \u25104  Eb 0 1 \u8805  Eb 0 1\cf0 \cb1 \strokec4 \
\cb3       simpa [this]\cb1 \
\cb3     \'b7 \cf5 \strokec5 -- (true,false)\cf0 \cb1 \strokec4 \
\cb3       exact le_rfl\cb1 \
\cb3     \'b7 \cf5 \strokec5 -- (true,true)\cf0 \cb1 \strokec4 \
\cb3       exact le_of_lt hLT11\cb1 \
\cb3   \'b7 exact hSym\cb1 \
\
\cf5 \cb3 \strokec5 ------------------------------------------------------------\cf0 \cb1 \strokec4 \
\cf5 \cb3 \strokec5 -- THEOREM 3 : existence of a real threshold \uc0\u964  decoding XOR\cf0 \cb1 \strokec4 \
\cf5 \cb3 \strokec5 ------------------------------------------------------------\cf0 \cb1 \strokec4 \
\
\cf5 \cb3 \strokec5 /-- Pure Boolean XOR truth table. -/\cf0 \cb1 \strokec4 \
\cf2 \cb3 \strokec2 def\cf0 \strokec4  XORbool (a b : Bool) : Bool :=\cb1 \
\cb3   (a && !b) || (!a && b)\cb1 \
\
\cf5 \cb3 \strokec5 /-- Energy gate with real threshold \uc0\u964 : [E(a,b) < \u964 ]. -/\cf0 \cb1 \strokec4 \
\cf2 \cb3 \strokec2 def\cf0 \strokec4  XORgate (p : Params) (\uc0\u964  : \u8477 ) (a b : Bool) : Bool :=\cb1 \
\cb3   decide (Eb p a b < \uc0\u964 )\cb1 \
\
\cf5 \cb3 \strokec5 /-- There exists \uc0\u964  such that XOR corners have E < \u964  < other corners. -/\cf0 \cb1 \strokec4 \
\cf2 \cb3 \strokec2 lemma\cf0 \strokec4  exists_XOR_threshold (p : Params) (h : isXORregion p) :\cb1 \
\cb3   \uc0\u8707  \u964 ,\cb1 \
\cb3     Eb p \cf2 \strokec2 true\cf0 \strokec4  \cf2 \strokec2 false\cf0 \strokec4  < \uc0\u964  \u8743 \cb1 \
\cb3     Eb p \cf2 \strokec2 false\cf0 \strokec4  \cf2 \strokec2 true\cf0 \strokec4  < \uc0\u964  \u8743 \cb1 \
\cb3     \uc0\u964  < Eb p \cf2 \strokec2 false\cf0 \strokec4  \cf2 \strokec2 false\cf0 \strokec4  \uc0\u8743 \cb1 \
\cb3     \uc0\u964  < Eb p \cf2 \strokec2 true\cf0 \strokec4  \cf2 \strokec2 true\cf0 \strokec4  := \cf2 \strokec2 by\cf0 \cb1 \strokec4 \
\cb3   rcases h \cf2 \strokec2 with\cf0 \strokec4  \uc0\u10216 hSym, hLT00, hLT11\u10217 \cb1 \
\cb3   \cf2 \strokec2 let\cf0 \strokec4  e : \uc0\u8477  := Eb p \cf2 \strokec2 true\cf0 \strokec4  \cf2 \strokec2 false\cf0 \cb1 \strokec4 \
\cb3   \cf2 \strokec2 let\cf0 \strokec4  m : \uc0\u8477  := min (Eb p \cf2 \strokec2 false\cf0 \strokec4  \cf2 \strokec2 false\cf0 \strokec4 ) (Eb p \cf2 \strokec2 true\cf0 \strokec4  \cf2 \strokec2 true\cf0 \strokec4 )\cb1 \
\cb3   \cf2 \strokec2 have\cf0 \strokec4  h_em : e < m := \cf2 \strokec2 by\cf0 \cb1 \strokec4 \
\cb3     \cf2 \strokec2 have\cf0 \strokec4  h1 : e < Eb p \cf2 \strokec2 false\cf0 \strokec4  \cf2 \strokec2 false\cf0 \strokec4  := \cf2 \strokec2 by\cf0 \strokec4  simpa [e] using hLT00\cb1 \
\cb3     \cf2 \strokec2 have\cf0 \strokec4  h2 : e < Eb p \cf2 \strokec2 true\cf0 \strokec4  \cf2 \strokec2 true\cf0 \strokec4   := \cf2 \strokec2 by\cf0 \strokec4  simpa [e] using hLT11\cb1 \
\cb3     exact lt_min h1 h2\cb1 \
\cb3   obtain \uc0\u10216 \u964 , h1, h2\u10217  := exists_between h_em\cb1 \
\cb3   \cf2 \strokec2 have\cf0 \strokec4  \uc0\u964 _lt_00 : \u964  < Eb p \cf2 \strokec2 false\cf0 \strokec4  \cf2 \strokec2 false\cf0 \strokec4  :=\cb1 \
\cb3     lt_of_lt_of_le h2 (min_le_left _ _)\cb1 \
\cb3   \cf2 \strokec2 have\cf0 \strokec4  \uc0\u964 _lt_11 : \u964  < Eb p \cf2 \strokec2 true\cf0 \strokec4  \cf2 \strokec2 true\cf0 \strokec4   :=\cb1 \
\cb3     lt_of_lt_of_le h2 (min_le_right _ _)\cb1 \
\cb3   \cf2 \strokec2 have\cf0 \strokec4  hSym' : Eb p \cf2 \strokec2 false\cf0 \strokec4  \cf2 \strokec2 true\cf0 \strokec4  = Eb p \cf2 \strokec2 true\cf0 \strokec4  \cf2 \strokec2 false\cf0 \strokec4  := \cf2 \strokec2 by\cf0 \cb1 \strokec4 \
\cb3     simpa [eq_comm] using hSym\cb1 \
\cb3   \cf2 \strokec2 have\cf0 \strokec4  ht1 : Eb p \cf2 \strokec2 false\cf0 \strokec4  \cf2 \strokec2 true\cf0 \strokec4  < \uc0\u964  := \cf2 \strokec2 by\cf0 \cb1 \strokec4 \
\cb3     simpa [hSym'] using h1\cb1 \
\cb3   refine \uc0\u10216 \u964 , ?_, ?_, ?_, ?_\u10217 \cb1 \
\cb3   \'b7 simpa [e] using h1\cb1 \
\cb3   \'b7 exact ht1\cb1 \
\cb3   \'b7 exact \uc0\u964 _lt_00\cb1 \
\cb3   \'b7 exact \uc0\u964 _lt_11\cb1 \
\
\cf5 \cb3 \strokec5 /-- Truth-table equality: with such \uc0\u964 , XORgate = XORbool. -/\cf0 \cb1 \strokec4 \
\cf2 \cb3 \strokec2 lemma\cf0 \strokec4  XORgate_truth_table (p : Params) \{\uc0\u964  : \u8477 \}\cb1 \
\cb3   (h_tf : Eb p \cf2 \strokec2 true\cf0 \strokec4  \cf2 \strokec2 false\cf0 \strokec4  < \uc0\u964 )\cb1 \
\cb3   (h_ft : Eb p \cf2 \strokec2 false\cf0 \strokec4  \cf2 \strokec2 true\cf0 \strokec4  < \uc0\u964 )\cb1 \
\cb3   (h00 : \uc0\u964  < Eb p \cf2 \strokec2 false\cf0 \strokec4  \cf2 \strokec2 false\cf0 \strokec4 )\cb1 \
\cb3   (h11 : \uc0\u964  < Eb p \cf2 \strokec2 true\cf0 \strokec4  \cf2 \strokec2 true\cf0 \strokec4 ) :\cb1 \
\cb3   \uc0\u8704  a b, XORgate p \u964  a b = XORbool a b := \cf2 \strokec2 by\cf0 \cb1 \strokec4 \
\cb3   intro a b\cb1 \
\cb3   cases a <;> cases b\cb1 \
\cb3   \'b7 \cf5 \strokec5 -- (false,false) \uc0\u8594  0\cf0 \cb1 \strokec4 \
\cb3     \cf2 \strokec2 have\cf0 \strokec4  : \'ac Eb p \cf2 \strokec2 false\cf0 \strokec4  \cf2 \strokec2 false\cf0 \strokec4  < \uc0\u964  := not_lt_of_ge (le_of_lt h00)\cb1 \
\cb3     simp [XORgate, XORbool, this]\cb1 \
\cb3   \'b7 \cf5 \strokec5 -- (false,true) \uc0\u8594  1\cf0 \cb1 \strokec4 \
\cb3     simp [XORgate, XORbool, h_ft]\cb1 \
\cb3   \'b7 \cf5 \strokec5 -- (true,false) \uc0\u8594  1\cf0 \cb1 \strokec4 \
\cb3     simp [XORgate, XORbool, h_tf]\cb1 \
\cb3   \'b7 \cf5 \strokec5 -- (true,true) \uc0\u8594  0\cf0 \cb1 \strokec4 \
\cb3     \cf2 \strokec2 have\cf0 \strokec4  : \'ac Eb p \cf2 \strokec2 true\cf0 \strokec4  \cf2 \strokec2 true\cf0 \strokec4  < \uc0\u964  := not_lt_of_ge (le_of_lt h11)\cb1 \
\cb3     simp [XORgate, XORbool, this]\cb1 \
\
\cf5 \cb3 \strokec5 /-- THEOREM 3 (formal):\cf0 \cb1 \strokec4 \
\cf5 \cb3 \strokec5     There exists a real \uc0\u964  such that the physical energy-gate\cf0 \cb1 \strokec4 \
\cf5 \cb3 \strokec5     \cf7 \strokec7 `(a,b) \uc0\u8614  [Eb(a,b) < \u964 ]`\cf5 \strokec5  realizes the XOR truth-table. -/\cf0 \cb1 \strokec4 \
\cf2 \cb3 \strokec2 theorem\cf0 \strokec4  XORgate_realizes_XOR (p : Params) (h : isXORregion p) :\cb1 \
\cb3   \uc0\u8707  \u964 , \u8704  a b, XORgate p \u964  a b = XORbool a b := \cf2 \strokec2 by\cf0 \cb1 \strokec4 \
\cb3   obtain \uc0\u10216 \u964 , h1, h2, h3, h4\u10217  := exists_XOR_threshold p h\cb1 \
\cb3   refine \uc0\u10216 \u964 , ?_\u10217 \cb1 \
\cb3   intro a b\cb1 \
\cb3   exact XORgate_truth_table p h1 h2 h3 h4 a b\cb1 \
\
\cf5 \cb3 \strokec5 ------------------------------------------------------------\cf0 \cb1 \strokec4 \
\cf5 \cb3 \strokec5 -- THEOREM 4 : Axis-strong convexity at XOR parameters\cf0 \cb1 \strokec4 \
\cf5 \cb3 \strokec5 ------------------------------------------------------------\cf0 \cb1 \strokec4 \
\
\cf5 \cb3 \strokec5 /-- XOR parameters used in the paper. -/\cf0 \cb1 \strokec4 \
\cf2 \cb3 \strokec2 def\cf0 \strokec4  pXOR : Params := \{ lam := \cf6 \strokec6 20\cf0 \strokec4 , kap := -\cf6 \strokec6 30\cf0 \strokec4  \}\cb1 \
\
\cf5 \cb3 \strokec5 /-- Bool \uc0\u8594  \u8477  via \{false\u8614 0, true\u8614 1\}. -/\cf0 \cb1 \strokec4 \
\cf2 \cb3 \strokec2 def\cf0 \strokec4  b2r (b : Bool) : \uc0\u8477  := \cf2 \strokec2 if\cf0 \strokec4  b \cf2 \strokec2 then\cf0 \strokec4  \cf6 \strokec6 1\cf0 \strokec4  \cf2 \strokec2 else\cf0 \strokec4  \cf6 \strokec6 0\cf0 \cb1 \strokec4 \
\
\cf5 \cb3 \strokec5 /-- For pXOR and any Boolean b, we have \uc0\u955 +\u954 \'b7b \u8800  0. -/\cf0 \cb1 \strokec4 \
\cf2 \cb3 \strokec2 lemma\cf0 \strokec4  lam_plus_kap_b2r_ne_zero (b : Bool) :\cb1 \
\cb3   pXOR.lam + pXOR.kap * b2r b \uc0\u8800  \cf6 \strokec6 0\cf0 \strokec4  := \cf2 \strokec2 by\cf0 \cb1 \strokec4 \
\cb3   cases b <;> simp [pXOR, b2r] <;> norm_num\cb1 \
\
\cf5 \cb3 \strokec5 /-- THEOREM 4 (formal, axis-strong convexity at XOR corners):\cf0 \cb1 \strokec4 \
\
\cf5 \cb3 \strokec5     For pXOR = (20,-30) and each Boolean corner (a,b),\cf0 \cb1 \strokec4 \
\cf5 \cb3 \strokec5     both second derivatives along x and y are strictly positive.\cf0 \cb1 \strokec4 \
\
\cf5 \cb3 \strokec5     This encodes \'93strict convexity along coordinate axes\'94 at each\cf0 \cb1 \strokec4 \
\cf5 \cb3 \strokec5     Boolean corner, matching the idea of a stable local minimum\cf0 \cb1 \strokec4 \
\cf5 \cb3 \strokec5     in the continuous energy landscape. -/\cf0 \cb1 \strokec4 \
\cf2 \cb3 \strokec2 theorem\cf0 \strokec4  XOR_axis_strict_convex_at_corners :\cb1 \
\cb3   \uc0\u8704  a b : Bool,\cb1 \
\cb3     \cf6 \strokec6 0\cf0 \strokec4  < d2E_dx2 pXOR (b2r a) (b2r b) \uc0\u8743 \cb1 \
\cb3     \cf6 \strokec6 0\cf0 \strokec4  < d2E_dy2 pXOR (b2r a) (b2r b) := \cf2 \strokec2 by\cf0 \cb1 \strokec4 \
\cb3   intro a b\cb1 \
\cb3   \cf2 \strokec2 have\cf0 \strokec4  hLy : pXOR.lam + pXOR.kap * b2r b \uc0\u8800  \cf6 \strokec6 0\cf0 \strokec4  :=\cb1 \
\cb3     lam_plus_kap_b2r_ne_zero b\cb1 \
\cb3   \cf2 \strokec2 have\cf0 \strokec4  hLx : pXOR.lam + pXOR.kap * b2r a \uc0\u8800  \cf6 \strokec6 0\cf0 \strokec4  :=\cb1 \
\cb3     lam_plus_kap_b2r_ne_zero a\cb1 \
\cb3   refine And.intro ?hx ?hy\cb1 \
\cb3   \'b7 \cf2 \strokec2 have\cf0 \strokec4  := d2E_dx2_pos pXOR (b2r a) (b2r b) hLy\cb1 \
\cb3     simpa using this\cb1 \
\cb3   \'b7 \cf2 \strokec2 have\cf0 \strokec4  := d2E_dy2_pos pXOR (b2r a) (b2r b) hLx\cb1 \
\cb3     simpa using this\cb1 \
\
\cf2 \cb3 \strokec2 end\cf0 \strokec4  Residual\cb1 \
\
\
\pard\tx720\tx1440\tx2160\tx2880\tx3600\tx4320\tx5040\tx5760\tx6480\tx7200\tx7920\tx8640\pardirnatural\partightenfactor0

\f1 \cf0 \kerning1\expnd0\expndtw0 \outl0\strokewidth0 \
}
