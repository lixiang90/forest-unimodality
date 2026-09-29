import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 85
  A := (-7299029860644010386749869/5000000000000000000000000)
  B := (12092794976826626990318303/125000000000000000000000000)
  C := (-36830572983908059850333139/10000000000000000000000000000)
  dδ := (16283200988026484690163187/250000000000000000000000000)
  dM := (268059593132740476249809/250000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(80295385094972004935698351/10000000000000000000000000), (33238199616599080066237093/10000000000000000000000000), (33117322422122050795678661/1000000000000000000000000), (39008073387995409575523809/1000000000000000000000000)]
  retention := ![(7/10), (3/5), (1/100), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (581/1216)
  hi := (23/48)
  vmin := (368935/1478656)
  damping := (368935/1478656)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell039
