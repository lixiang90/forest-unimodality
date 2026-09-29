import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 51
  A := (-35083179302975366963934789/50000000000000000000000000)
  B := (46833221439763449145399221/500000000000000000000000000)
  C := (63702287916342359430643683/100000000000000000000000000000)
  dδ := (3600870661217484003380207/40000000000000000000000000)
  dM := (3044162873730300779978597/2000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(50241630992053742943426187/10000000000000000000000000), (30550352038424355427537193/10000000000000000000000000), (42129763367280766317435337/1000000000000000000000000)]
  retention := ![(7/10), (3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (407/808)
  hi := (51/101)
  vmin := (2550/10201)
  damping := (2550/10201)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell066
