import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 19
  A := (11383090189556533845305353/100000000000000000000000000)
  B := (1486712290416897577771671/100000000000000000000000000)
  C := (-20083768434928428447960869/1000000000000000000000000000)
  dδ := (1960253996616890918847087/125000000000000000000000000)
  dM := (20862129998307719756399023/250000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(557057546338823650344807/250000000000000000000000), (3419449002308364016222697/1250000000000000000000000)]
  retention := ![(9/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (1/4)
  hi := (9/35)
  vmin := (3/16)
  damping := (7500000000000000000000000000000000000000/98696044010893586188807139859649302879409)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell000
