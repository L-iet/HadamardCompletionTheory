/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import CompletionCodeTrap.CodeTrapMatrixCode
public import CompletionCodeTrap.CodeTrapDeletionData
public import CompletionTheory.EncodedFrames
public import Mathlib.Tactic.NormNum
@[expose] public section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CompletionTheory
instance trapFivePrime : Fact (Nat.Prime 5) := ⟨by decide⟩
def trapOldBasis : Matrix (Fin 10) (Fin 20) (ZMod 5) := ![
  ![1,0,0,0,0,0,0,0,0,0,3,2,2,4,4,0,0,1,3,0],
  ![0,1,0,0,0,0,0,0,0,0,4,3,0,1,0,1,4,0,1,0],
  ![0,0,1,0,0,0,0,0,0,0,1,2,3,0,3,1,1,0,0,3],
  ![0,0,0,1,0,0,0,0,0,0,2,4,4,0,2,4,2,1,3,2],
  ![0,0,0,0,1,0,0,0,0,0,1,2,0,3,3,4,2,4,0,0],
  ![0,0,0,0,0,1,0,0,0,0,0,3,3,1,0,0,4,2,4,2],
  ![0,0,0,0,0,0,1,0,0,0,2,2,0,0,0,1,4,3,4,3],
  ![0,0,0,0,0,0,0,1,0,0,0,2,2,2,1,1,3,3,4,1],
  ![0,0,0,0,0,0,0,0,1,0,0,4,1,3,2,2,3,2,1,1],
  ![0,0,0,0,0,0,0,0,0,1,3,2,1,2,1,2,3,0,1,4]
]
def trapNewBasis : Matrix (Fin 10) (Fin 20) (ZMod 5) := ![
  ![1,0,0,0,0,0,0,0,0,3,2,0,3,1,1,3,0,1,0,0],
  ![0,1,0,0,0,0,0,0,0,3,3,0,2,0,0,3,1,0,1,1],
  ![0,0,1,0,0,0,0,0,0,3,0,0,4,2,0,4,1,0,2,3],
  ![0,0,0,1,0,0,0,0,0,4,4,0,0,2,2,0,3,1,3,0],
  ![0,0,0,0,1,0,0,0,0,1,4,0,0,3,1,2,3,4,3,3],
  ![0,0,0,0,0,1,0,0,0,3,4,0,0,0,0,2,1,2,4,3],
  ![0,0,0,0,0,0,1,0,0,0,2,0,2,4,1,4,3,3,0,0],
  ![0,0,0,0,0,0,0,1,0,0,0,0,4,1,2,4,2,3,0,3],
  ![0,0,0,0,0,0,0,0,1,4,2,0,2,0,2,3,4,2,1,4],
  ![0,0,0,0,0,0,0,0,0,0,0,1,4,3,2,1,3,0,2,4]
]
def trapOldInformation : Fin 10 → Fin 20 := ![0,1,2,3,4,5,6,7,8,9]
def trapNewInformation : Fin 10 → Fin 20 := ![0,1,2,3,4,5,6,7,8,11]
def trapInformationSelector (J : Fin 10 → Fin 20) : Matrix (Fin 10) (Fin 20) (ZMod 5) := fun i j => if j=J i then 1 else 0
def trapCompletedMasks : Fin 20 → ℕ := ![0,965904,1003736,730036,501868,412530,210762,358790,694982,250934,7676,126672,307898,444300,581982,645928,683178,816740,855582,886242]
def trapCompletedIntegerMatrix : Matrix (Fin 20) (Fin 20) ℤ := encodedIntFrame trapCompletedMasks

def trapCompletedFieldMatrix : Matrix (Fin 20) (Fin 20) (ZMod 5) :=
  trapCompletedIntegerMatrix.map (Int.castRingHom (ZMod 5))

def trapOldFieldMatrix : Matrix (Fin 12) (Fin 20) (ZMod 5) :=
  codeTrapOldIntegerMatrix.map (Int.castRingHom (ZMod 5))

def trapElevenToTwenty (i : Fin 11) : Fin 20 := ⟨i.val,Nat.lt_trans i.isLt (by decide)⟩
def trapTenToTwenty (i : Fin 10) : Fin 20 := ⟨i.val,Nat.lt_trans i.isLt (by decide)⟩
def trapRetainedPivotMatrix : Matrix (Fin 11) (Fin 20) (ZMod 5) :=
  fun i => trapCompletedFieldMatrix (trapElevenToTwenty i)
def trapOldBasisFromRows : Matrix (Fin 10) (Fin 12) (ZMod 5) := ![
  ![0,4,0,1,4,4,0,4,0,0,4,0],
  ![4,4,4,1,2,3,0,3,0,0,4,0],
  ![3,1,2,1,0,3,2,0,0,1,2,0],
  ![4,2,3,3,3,0,2,4,0,1,3,0],
  ![3,0,1,2,0,4,1,0,0,2,2,0],
  ![1,2,2,1,3,1,3,2,0,4,1,0],
  ![0,0,3,0,4,3,3,4,0,4,4,0],
  ![1,3,0,0,3,3,4,2,0,3,1,0],
  ![0,2,4,3,0,1,4,0,0,3,3,0],
  ![0,2,1,3,1,3,1,1,0,2,1,0]
]
def trapNewBasisFromRows : Matrix (Fin 10) (Fin 20) (ZMod 5) := ![
  ![1,0,3,4,3,4,0,3,1,0,2,0,0,0,0,0,0,0,0,0],
  ![2,0,2,1,2,1,0,2,4,0,1,0,0,0,0,0,0,0,0,0],
  ![4,2,0,0,2,1,1,4,4,0,2,0,0,0,0,0,0,0,0,0],
  ![3,0,2,0,2,0,0,2,3,0,3,0,0,0,0,0,0,0,0,0],
  ![1,2,2,2,2,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0],
  ![4,3,0,2,0,4,4,1,1,0,1,0,0,0,0,0,0,0,0,0],
  ![4,0,3,2,3,2,1,2,0,0,3,0,0,0,0,0,0,0,0,0],
  ![0,3,0,1,3,3,4,1,2,0,3,0,0,0,0,0,0,0,0,0],
  ![4,0,3,2,3,2,1,4,3,0,3,0,0,0,0,0,0,0,0,0],
  ![3,0,0,1,0,3,4,1,2,0,1,0,0,0,0,0,0,0,0,0]
]
def trapNewBasisFromRetainedPivot : Matrix (Fin 10) (Fin 11) (ZMod 5) := ![
  ![1,0,3,4,3,4,0,3,1,0,2],
  ![2,0,2,1,2,1,0,2,4,0,1],
  ![4,2,0,0,2,1,1,4,4,0,2],
  ![3,0,2,0,2,0,0,2,3,0,3],
  ![1,2,2,2,2,0,0,0,0,0,1],
  ![4,3,0,2,0,4,4,1,1,0,1],
  ![4,0,3,2,3,2,1,2,0,0,3],
  ![0,3,0,1,3,3,4,1,2,0,3],
  ![4,0,3,2,3,2,1,4,3,0,3],
  ![3,0,0,1,0,3,4,1,2,0,1]
]
noncomputable def trapOldCode : Submodule (ZMod 5) (Fin 20 → ZMod 5) := trapMatrixCode trapOldBasis
noncomputable def trapNewSpanCode : Submodule (ZMod 5) (Fin 20 → ZMod 5) := trapMatrixCode trapNewBasis

def trapPivotVector : Fin 20 → ZMod 5 := trapCompletedFieldMatrix 10
end CompletionTheory
