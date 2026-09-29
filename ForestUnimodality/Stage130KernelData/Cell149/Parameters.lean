import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 76
  A := (-16735093312299926149222529/10000000000000000000000000)
  B := (1425871937321463410464073/12500000000000000000000000)
  C := (19633390494776810066219/3906250000000000000000000)
  dδ := (70150900749983910453799751/1000000000000000000000000000)
  dM := (2718379364385008212234851/2000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(14850046256320781346005333/2500000000000000000000000), (76945406224703445374757393/10000000000000000000000000), (48013258707932973123888587/10000000000000000000000000), (55825490920194724253633467/1000000000000000000000000)]
  retention := ![(7/10), (3/5), (1/100), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (28/53)
  hi := (95449/180624)
  vmin := (8129868575/32625029376)
  damping := (8129868575/32625029376)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell149
