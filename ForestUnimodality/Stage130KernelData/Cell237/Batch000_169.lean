import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell237.Parameters
import ForestUnimodality.BinomialMassData.Q41_63.Batch000_049
import ForestUnimodality.BinomialMassData.Q41_63.Batch050_099
import ForestUnimodality.BinomialMassData.Q41_63.Batch100_149
import ForestUnimodality.BinomialMassData.Q41_63.Batch150_199
import ForestUnimodality.BinomialMassData.Q83_126.Batch000_049
import ForestUnimodality.BinomialMassData.Q83_126.Batch050_099
import ForestUnimodality.BinomialMassData.Q83_126.Batch100_149
import ForestUnimodality.BinomialMassData.Q83_126.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree000.table
  base := (397302639924047512109517299/50000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (943)
      previous := (0)
      next := (506)
      square := (17543973695327667802756899000000000000000)
      linear := (-36449063261819730427659713820000000000000)
      constant := (5006013263042998652579917967400000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree000.table
  base := (397302639924047512109517299/50000000000000000000000000)
  polynomial :=
    { denominator := 1260000000000000000000000000000000000000000
      center := (1909)
      previous := (0)
      next := (989)
      square := (35087947390655335605513798000000000000000)
      linear := (-72898126523639460855319427640000000000000)
      constant := (10012026526085997305159835934800000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 0 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 0 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree001.table
  base := (1959762833428888379725055155095418398841/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-3734896828511511776768627688660000000000000)
      constant := (250868087316185877130073446217978899999997728) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree001.table
  base := (7813874471153679519163295862365800579491/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-7504881604413678889142769175320000000000000)
      constant := (500196766466772018504832111589237799999996464) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 1 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 1 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (30184421155165788947/100000000000000000000)
  directionHi := (7546105288791447237/25000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree002.table
  base := (49335922548362369696835750779889921894683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-5173502671528380536594693406660000000000000)
      constant := (200675570879179514623487562630623099999996827) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree002.table
  base := (24507946725182585900697386008882980599647/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-10417181237838071744400414409320000000000000)
      constant := (398975545910051675788024872365146199999995772) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 2 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 2 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30184421155165788947/100000000000000000000)
  centralHi := (7546105288791447237/25000000000000000000)
  directionLo := (10671804442504205793/25000000000000000000)
  directionHi := (42687217770016823173/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree003.table
  base := (1931669482134807055316828589488633866833/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6601)
      previous := (0)
      next := (3542)
      square := (122807815867293674619298293000000000000000)
      linear := (-734678723838361032935639902740000000000000)
      constant := (18003579804655547394158703727829750705467060) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree003.table
  base := (9562926742142516630908325860802798823821/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (13363)
      previous := (0)
      next := (6923)
      square := (245615631734587349238596586000000000000000)
      linear := (-1481053430140273844406451071480000000000000)
      constant := (35705639429753527910066907284432274250440488) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 3 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 3 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10671804442504205793/25000000000000000000)
  centralHi := (42687217770016823173/100000000000000000000)
  directionLo := (52280951037804008779/100000000000000000000)
  directionHi := (2614047551890200439/5000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree004.table
  base := (30053477330497000066784887719162930756319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-8050714357562118056246824842660000000000000)
      constant := (132749782288721234661918897431837672171830111) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree004.table
  base := (926516668582782428557176509225170750389/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-16241780504686857454915704877320000000000000)
      constant := (262798503888011678984609411531580973330812224) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 4 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 4 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52280951037804008779/100000000000000000000)
  centralHi := (2614047551890200439/5000000000000000000)
  directionLo := (12073768462066315579/20000000000000000000)
  directionHi := (7546105288791447237/12500000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree005.table
  base := (11584932562091392803245978206531495938757/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-9489320200578986816072890560660000000000000)
      constant := (111136197004429842070326636661547014761853066) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree005.table
  base := (11383402583495957901315841500452119142353/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-19154080138111250310173350111320000000000000)
      constant := (219829505666679933128529453358977843503996228) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 5 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 5 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12073768462066315579/20000000000000000000)
  centralHi := (7546105288791447237/12500000000000000000)
  directionLo := (67494417564433431477/100000000000000000000)
  directionHi := (33747208782216715739/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree006.table
  base := (17660581723774767207956314178887934130139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6601)
      previous := (0)
      next := (3542)
      square := (122807815867293674619298293000000000000000)
      linear := (-1214214004843983952877661808740000000000000)
      constant := (10657062033267796372076471315969578951391299) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree006.table
  base := (8637593127112674293720360002952019814661/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (13363)
      previous := (0)
      next := (6923)
      square := (245615631734587349238596586000000000000000)
      linear := (-2451819974615071462825666149480000000000000)
      constant := (21090401642971649315348212137247362953062004) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 6 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 6 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67494417564433431477/100000000000000000000)
  centralHi := (33747208782216715739/50000000000000000000)
  directionLo := (18484107502856541973/25000000000000000000)
  directionHi := (73936430011426167893/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree007.table
  base := (264485588077785604920147097325524262743/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8487)
      previous := (0)
      next := (4554)
      square := (157895763257949010224812091000000000000000)
      linear := (-1766647412373246333675003142380000000000000)
      constant := (12269402435944920799957368166798612848764050) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree007.table
  base := (6432893098053902578599053765088949004697/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11340000000000000000000000000000000000000000
      center := (17181)
      previous := (0)
      next := (8901)
      square := (315791526515898020449624182000000000000000)
      linear := (-3568382772137148002955520082760000000000000)
      constant := (24329542396401305534491314475781736342652796) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 7 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 7 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18484107502856541973/25000000000000000000)
  centralHi := (73936430011426167893/100000000000000000000)
  directionLo := (79860471845005650117/100000000000000000000)
  directionHi := (39930235922502825059/50000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree008.table
  base := (4822075866601822871960658067700914616543/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-13805137729629593095551087714660000000000000)
      constant := (80192468535122963964750029906369860226118334) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree008.table
  base := (931729754085025196370374990447905342337/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-27890979038384428875946285813320000000000000)
      constant := (159552313078571469532832970222234726074711060) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 8 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 8 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79860471845005650117/100000000000000000000)
  centralHi := (39930235922502825059/50000000000000000000)
  directionLo := (10671804442504205793/12500000000000000000)
  directionHi := (17074887108006729269/20000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree009.table
  base := (1349551472683827328171918339358984067071/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6601)
      previous := (0)
      next := (3542)
      square := (122807815867293674619298293000000000000000)
      linear := (-1693749285849606872819683714740000000000000)
      constant := (8683232559837563859929463521906559867891555) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree009.table
  base := (1290849302442100106566549976524647940127/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (13363)
      previous := (0)
      next := (6923)
      square := (245615631734587349238596586000000000000000)
      linear := (-3422586519089869081244881227480000000000000)
      constant := (17350805873580149344967975730033697415960070) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 9 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 9 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10671804442504205793/12500000000000000000)
  centralHi := (17074887108006729269/20000000000000000000)
  directionLo := (90553263465497366843/100000000000000000000)
  directionHi := (22638315866374341711/25000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree010.table
  base := (4397898992881427137791280868224692588439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-16682349415663330615203219150660000000000000)
      constant := (79211154471593758827193357732183804883514391) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree010.table
  base := (1034363004083992362092654239719906763113/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-33715578305233214586461576281320000000000000)
      constant := (159016796602756971175165009740186479542363976) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 10 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 10 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90553263465497366843/100000000000000000000)
  centralHi := (22638315866374341711/25000000000000000000)
  directionLo := (5965720044005912541/6250000000000000000)
  directionHi := (95451520704094600657/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree011.table
  base := (2485355955467156975798623647967394791109/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-18120955258680199375029284868660000000000000)
      constant := (82945156010446399360589998564602589925911621) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree011.table
  base := (2256451434436480455483845706615274181589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-36627877938657607441719221515320000000000000)
      constant := (167254092032221915757324288655272046453453482) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 11 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 11 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5965720044005912541/6250000000000000000)
  centralHi := (95451520704094600657/100000000000000000000)
  directionLo := (25027599871437707727/25000000000000000000)
  directionHi := (100110399485750830909/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree012.table
  base := (461560764633667221639839935578554442743/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6601)
      previous := (0)
      next := (3542)
      square := (122807815867293674619298293000000000000000)
      linear := (-2173284566855229792761705620740000000000000)
      constant := (9889529775093245359578554853340285018499326) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree012.table
  base := (36175732565714447427186993843447047001/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (13363)
      previous := (0)
      next := (6923)
      square := (245615631734587349238596586000000000000000)
      linear := (-4393353063564666699664096305480000000000000)
      constant := (20019193055130720130189891943478405909097640) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 12 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 12 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25027599871437707727/25000000000000000000)
  centralHi := (100110399485750830909/100000000000000000000)
  directionLo := (52280951037804008779/50000000000000000000)
  directionHi := (104561902075608017559/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree013.table
  base := (-179080880855072764504895414206881426069/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-20998166944713936894681416304660000000000000)
      constant := (97117710545559520434213953065085775239864278) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree013.table
  base := (-106216474906722019716159348506362310217/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-42452477205506393152234511983320000000000000)
      constant := (197219263553169813520890584516062479907487270) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 13 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 13 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52280951037804008779/50000000000000000000)
  centralHi := (104561902075608017559/100000000000000000000)
  directionLo := (108831478195150231411/100000000000000000000)
  directionHi := (27207869548787557853/25000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree014.table
  base := (-1413818524567940872024160760682206614837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8487)
      previous := (0)
      next := (4554)
      square := (157895763257949010224812091000000000000000)
      linear := (-3205253255390115093501068860380000000000000)
      constant := (15294485764859555232378996145933188849387421) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree014.table
  base := (-312558089237416091394044416360800085207/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11340000000000000000000000000000000000000000
      center := (17181)
      previous := (0)
      next := (8901)
      square := (315791526515898020449624182000000000000000)
      linear := (-6480682405561540858213165316760000000000000)
      constant := (31136214532621993455718897811354263516876310) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 14 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 14 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108831478195150231411/100000000000000000000)
  centralHi := (27207869548787557853/25000000000000000000)
  directionLo := (56469881190360849501/50000000000000000000)
  directionHi := (112939762380721699003/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree015.table
  base := (-2288007356672885953596365145687376639199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6601)
      previous := (0)
      next := (3542)
      square := (122807815867293674619298293000000000000000)
      linear := (-2652819847860852712703727526740000000000000)
      constant := (13184619103140260134177237073451866902113241) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree015.table
  base := (-150983576545371822908683962447600213713/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (13363)
      previous := (0)
      next := (6923)
      square := (245615631734587349238596586000000000000000)
      linear := (-5364119608039464318083311383480000000000000)
      constant := (26891685183119692904032618129539465784082144) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 15 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 15 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56469881190360849501/50000000000000000000)
  centralHi := (112939762380721699003/100000000000000000000)
  directionLo := (2922594011221698527/2500000000000000000)
  directionHi := (116903760448867941081/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree016.table
  base := (-3015995333843578927207084044257491354551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-25313984473764543174159613458660000000000000)
      constant := (131778250244371868105875615822262016813787081) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree016.table
  base := (-625012130457633016699434391129701572797/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-51189376105779571718007447685320000000000000)
      constant := (269155333327648621339077762985022144575687070) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 16 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 16 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2922594011221698527/2500000000000000000)
  centralHi := (116903760448867941081/100000000000000000000)
  directionLo := (12073768462066315579/10000000000000000000)
  directionHi := (120737684620663155791/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree017.table
  base := (-906491014576434708283091935894736932903/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-26752590316781411933985679176660000000000000)
      constant := (146299582523111588450638775915275156453231972) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree017.table
  base := (-3718756224976681541425615973611533682019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-54101675739203964573265092919320000000000000)
      constant := (299121773519002866236421222267991645632133178) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 17 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 17 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12073768462066315579/10000000000000000000)
  centralHi := (120737684620663155791/100000000000000000000)
  directionLo := (3889173645964899637/3125000000000000000)
  directionHi := (24890711334175357677/20000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree018.table
  base := (-4140444964403499946472645138998363850491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6601)
      previous := (0)
      next := (3542)
      square := (122807815867293674619298293000000000000000)
      linear := (-3132355128866475632645749432740000000000000)
      constant := (18015126833507737033779001294941721541933469) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree018.table
  base := (-843828135900957374475338451183329556299/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (13363)
      previous := (0)
      next := (6923)
      square := (245615631734587349238596586000000000000000)
      linear := (-6334886152514261936502526461480000000000000)
      constant := (36860815218456654227610206270401516656721410) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 18 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 18 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3889173645964899637/3125000000000000000)
  centralHi := (24890711334175357677/20000000000000000000)
  directionLo := (32015413327512617379/25000000000000000000)
  directionHi := (128061653310050469517/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree019.table
  base := (-4577460934024042758595563858214086868593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-29629802002815149453637810612660000000000000)
      constant := (179216394361535783295754129605528289218554383) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree019.table
  base := (-4644012730134564540010850992449052198043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-59926275006052750283780383387320000000000000)
      constant := (366890737475157268240753011874579423651934666) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 19 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 19 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32015413327512617379/25000000000000000000)
  centralHi := (128061653310050469517/100000000000000000000)
  directionLo := (65785420742319457321/50000000000000000000)
  directionHi := (131570841484638914643/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree020.table
  base := (-990287007947037308170238511836179131079/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-31068407845832018213463876330660000000000000)
      constant := (197483095927988363737879707265011025143737245) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree020.table
  base := (-5007574308086941199772843486625416400101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-62838574639477143139038028621320000000000000)
      constant := (404439240116113291022284252744367444615998262) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 20 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 20 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65785420742319457321/50000000000000000000)
  centralHi := (131570841484638914643/100000000000000000000)
  directionLo := (67494417564433431477/50000000000000000000)
  directionHi := (26997767025773372591/20000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree021.table
  base := (-5273914466417110035490668568820459411701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (943)
      previous := (0)
      next := (506)
      square := (17543973695327667802756899000000000000000)
      linear := (-515984344267442650369681619820000000000000)
      constant := (3442705006732348336545920326704311057062837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree021.table
  base := (-1330290570984985768071871517551066905789/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1260000000000000000000000000000000000000000
      center := (1909)
      previous := (0)
      next := (989)
      square := (35087947390655335605513798000000000000000)
      linear := (-1043664670998437079274534505640000000000000)
      constant := (7052426235084596575456599793674262279482344) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 21 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 21 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67494417564433431477/50000000000000000000)
  centralHi := (26997767025773372591/20000000000000000000)
  directionLo := (138322394751973624287/100000000000000000000)
  directionHi := (4322574835999175759/3125000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree022.table
  base := (-5554147614129176845548150049380949856629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-33945619531865755733116007766660000000000000)
      constant := (237401645950148913548851375811647010019039499) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree022.table
  base := (-5593830083939180382036666220260548022893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-68663173906325928849553319089320000000000000)
      constant := (486409709460268493973260391852891769794275366) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 22 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 22 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (138322394751973624287/100000000000000000000)
  centralHi := (4322574835999175759/3125000000000000000)
  directionLo := (35394371171834336301/25000000000000000000)
  directionHi := (28315496937467469041/20000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree023.table
  base := (-5799544469273281068011225181165384495549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-35384225374882624492942073484660000000000000)
      constant := (258987377269992151106311155465214588937166019) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree023.table
  base := (-5832810309899174115815885117278786129633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-71575473539750321704810964323320000000000000)
      constant := (530702397672726352587585378927920995702973246) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 23 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 23 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35394371171834336301/25000000000000000000)
  centralHi := (28315496937467469041/20000000000000000000)
  directionLo := (144759398488891423273/100000000000000000000)
  directionHi := (72379699244445711637/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree024.table
  base := (-120320881770278118657933128860754399601/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6601)
      previous := (0)
      next := (3542)
      square := (122807815867293674619298293000000000000000)
      linear := (-4091425690877721472529793244740000000000000)
      constant := (31291559696418480437203976584940365488797950) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree024.table
  base := (-1208776589059199036444255615873288216383/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (13363)
      previous := (0)
      next := (6923)
      square := (245615631734587349238596586000000000000000)
      linear := (-8276419241463857173340956617480000000000000)
      constant := (64126115104318901024922736230158798965750970) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 24 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 24 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (144759398488891423273/100000000000000000000)
  centralHi := (72379699244445711637/50000000000000000000)
  directionLo := (18484107502856541973/12500000000000000000)
  directionHi := (29574572004570467157/20000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree025.table
  base := (-3104204055615465081845444831209822256327/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-38261437060916362012594204920660000000000000)
      constant := (305292726996772693380907573720356430929276274) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree025.table
  base := (-62316685921012344242587944577634202357/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-77400072806599107415326254791320000000000000)
      constant := (625670945920249275771636907333273970169013400) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 25 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 25 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18484107502856541973/12500000000000000000)
  centralHi := (29574572004570467157/20000000000000000000)
  directionLo := (75461052887914472369/50000000000000000000)
  directionHi := (150922105775828944739/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree026.table
  base := (-1276091064117689014766086477234348591731/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-39700042903933230772420270638660000000000000)
      constant := (329978289706632981021497010379404352197098305) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree026.table
  base := (-799982766701612808197648975016325706043/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-80312372440023500270583900025320000000000000)
      constant := (676280797633244243899026633300123252363445328) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 26 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 26 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75461052887914472369/50000000000000000000)
  centralHi := (150922105775828944739/100000000000000000000)
  directionLo := (76955476238346612779/50000000000000000000)
  directionHi := (153910952476693225559/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree027.table
  base := (-816906148837725298989033625311575225969/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6601)
      previous := (0)
      next := (3542)
      square := (122807815867293674619298293000000000000000)
      linear := (-4570960971883344392471815150740000000000000)
      constant := (39518729607620372871755852022760762602781368) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree027.table
  base := (-3275709511845482612581853898934474120453/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (13363)
      previous := (0)
      next := (6923)
      square := (245615631734587349238596586000000000000000)
      linear := (-9247185785938654791760171695480000000000000)
      constant := (80993458965012733793516485241959587651520908) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 27 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 27 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76955476238346612779/50000000000000000000)
  centralHi := (153910952476693225559/100000000000000000000)
  directionLo := (156842853113412026337/100000000000000000000)
  directionHi := (78421426556706013169/50000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree028.table
  base := (-6675247915564048551476492468746917261729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8487)
      previous := (0)
      next := (4554)
      square := (157895763257949010224812091000000000000000)
      linear := (-6082464941423852613153200296380000000000000)
      constant := (54621971530095059508443416892700497912599657) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree028.table
  base := (-3344351939679469454757600181957799819691/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11340000000000000000000000000000000000000000
      center := (17181)
      previous := (0)
      next := (8901)
      square := (315791526515898020449624182000000000000000)
      linear := (-12305281672410326568728455784760000000000000)
      constant := (111947596392275383550319256407559710008940812) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 28 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 28 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156842853113412026337/100000000000000000000)
  centralHi := (78421426556706013169/50000000000000000000)
  directionLo := (79860471845005650117/50000000000000000000)
  directionHi := (31944188738002260047/20000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree029.table
  base := (-6802424479167181122672479775597373915959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-44015860432983837051898467792660000000000000)
      constant := (410026161659414924805477883235634022927558729) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree029.table
  base := (-851701132313868296281942921725639664947/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-89049271340296678836356835727320000000000000)
      constant := (840341908278719938834627357501974978717205712) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 29 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 29 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79860471845005650117/50000000000000000000)
  centralHi := (31944188738002260047/20000000000000000000)
  directionLo := (162548082528525019217/100000000000000000000)
  directionHi := (81274041264262509609/50000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree030.table
  base := (-138367255788624298187570003611401775741/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6601)
      previous := (0)
      next := (3542)
      square := (122807815867293674619298293000000000000000)
      linear := (-5050496252888967312413837056740000000000000)
      constant := (48742151420477482425370190275768590844910950) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree030.table
  base := (-277105973012992626687510043148807217903/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (13363)
      previous := (0)
      next := (6923)
      square := (245615631734587349238596586000000000000000)
      linear := (-10217952330413452410179386773480000000000000)
      constant := (99895034120605307438901080888768800845238850) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 30 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 30 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (162548082528525019217/100000000000000000000)
  centralHi := (81274041264262509609/50000000000000000000)
  directionLo := (5166465109975139501/3125000000000000000)
  directionHi := (165326883519204464033/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree031.table
  base := (-7024334677609386272202021050455729524593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-46893072119017574571550599228660000000000000)
      constant := (468308356187068572512414368008961209516890383) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree031.table
  base := (-7032037454976436969506435876189559937467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-94873870607145464546872126195320000000000000)
      constant := (959763744156764953035615073132167273216386954) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 31 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 31 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5166465109975139501/3125000000000000000)
  centralHi := (165326883519204464033/100000000000000000000)
  directionLo := (168059744420384683169/100000000000000000000)
  directionHi := (16805974442038468317/10000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree032.table
  base := (-890170199248651339377529924453143673193/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-48331677962034443331376664946660000000000000)
      constant := (498909087731537467822837254882603782088775864) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree032.table
  base := (-44548403983190171919761396601195372937/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-97786170240569857402129771429320000000000000)
      constant := (1022459510187684925519798501374673780740175040) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 32 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 32 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (168059744420384683169/100000000000000000000)
  centralHi := (16805974442038468317/10000000000000000000)
  directionLo := (10671804442504205793/6250000000000000000)
  directionHi := (170748871080067292689/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree033.table
  base := (-7210264058083606898829128707172142486533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6601)
      previous := (0)
      next := (3542)
      square := (122807815867293674619298293000000000000000)
      linear := (-5530031533894590232355858962740000000000000)
      constant := (58942033419528583732678594924077085163438947) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree033.table
  base := (-7215548751936712866047039100961243836923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (13363)
      previous := (0)
      next := (6923)
      square := (245615631734587349238596586000000000000000)
      linear := (-11188718874888250028598601851480000000000000)
      constant := (120792936707762677233537820470672182935833914) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 33 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 33 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10671804442504205793/6250000000000000000)
  centralHi := (170748871080067292689/100000000000000000000)
  directionLo := (43349074568834411197/25000000000000000000)
  directionHi := (173396298275337644789/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree034.table
  base := (-1458340261229726790129366100352785968929/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-51208889648068180851028796382660000000000000)
      constant := (563013378811027631151089662631578962446603995) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree034.table
  base := (-7296072962032436693095019601202400917371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-103610769507418643112645061897320000000000000)
      constant := (1153789558034002295512387069471695341517909002) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 34 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 34 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43349074568834411197/25000000000000000000)
  centralHi := (173396298275337644789/100000000000000000000)
  directionLo := (44000976932380632591/25000000000000000000)
  directionHi := (35200781545904506073/20000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree035.table
  base := (-3683101544200370772463182335388973090719/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8487)
      previous := (0)
      next := (4554)
      square := (157895763257949010224812091000000000000000)
      linear := (-7521070784440721372979266014380000000000000)
      constant := (85216031322677073105125734839768904515124654) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree035.table
  base := (-460613536076741256446227306456761817003/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11340000000000000000000000000000000000000000
      center := (17181)
      previous := (0)
      next := (8901)
      square := (315791526515898020449624182000000000000000)
      linear := (-15217581305834719423986101018760000000000000)
      constant := (174630704237179216288841040224448513592297568) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 35 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 35 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44000976932380632591/25000000000000000000)
  centralHi := (35200781545904506073/20000000000000000000)
  directionLo := (178573443760640682589/100000000000000000000)
  directionHi := (17857344376064068259/10000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree036.table
  base := (-3717097588558602951320043403819091287943/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6601)
      previous := (0)
      next := (3542)
      square := (122807815867293674619298293000000000000000)
      linear := (-6009566814900213152297880868740000000000000)
      constant := (70108125803191598447493279856311561484034274) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree036.table
  base := (-7437179740743823531574043453231350008927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (13363)
      previous := (0)
      next := (6923)
      square := (245615631734587349238596586000000000000000)
      linear := (-12159485419363047647017816929480000000000000)
      constant := (143667707656859302139354464046489949292126386) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 36 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 36 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (178573443760640682589/100000000000000000000)
  centralHi := (17857344376064068259/10000000000000000000)
  directionLo := (90553263465497366843/50000000000000000000)
  directionHi := (181106526930994733687/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree037.table
  base := (-7496019834592023260313961903444034052071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-55524707177118787130506993536660000000000000)
      constant := (666394759281937382962996232067170628847330201) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree037.table
  base := (-1499696636282381659948178596890438016687/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-112347668407691821678417997599320000000000000)
      constant := (1365570329842974818680477768677138515117692970) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 37 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 37 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90553263465497366843/50000000000000000000)
  centralHi := (181106526930994733687/100000000000000000000)
  directionLo := (91802333000691682819/50000000000000000000)
  directionHi := (183604666001383365639/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree038.table
  base := (-3775976120294863962927541859371689198763/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-56963313020135655890333059254660000000000000)
      constant := (702776008229893065874467028823867531140219306) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree038.table
  base := (-188849600518162160710578216763553811387/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-115259968041116214533675642833320000000000000)
      constant := (1440095771423555487199775055435516393808399760) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 38 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 38 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91802333000691682819/50000000000000000000)
  centralHi := (183604666001383365639/100000000000000000000)
  directionLo := (46517317110104249321/25000000000000000000)
  directionHi := (37213853688083399457/20000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree039.table
  base := (-950276709964213587293421906952761618943/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6601)
      previous := (0)
      next := (3542)
      square := (122807815867293674619298293000000000000000)
      linear := (-6489102095905836072239902774740000000000000)
      constant := (82235111199333398290920868731290657008369096) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree039.table
  base := (-760388842549293935717890675567742067397/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (13363)
      previous := (0)
      next := (6923)
      square := (245615631734587349238596586000000000000000)
      linear := (-13130251963837845265437032007480000000000000)
      constant := (168509339677930511882763265825252514965558460) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 39 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 39 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46517317110104249321/25000000000000000000)
  centralHi := (37213853688083399457/20000000000000000000)
  directionLo := (188501649696824618569/100000000000000000000)
  directionHi := (18850164969682461857/10000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree040.table
  base := (-955872766228854806237612390159915587579/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-59840524706169393409985190690660000000000000)
      constant := (778414030580106320765053762852442360263191592) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree040.table
  base := (-1529672347504506897939640934331644194927/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-121084567307965000244190933301320000000000000)
      constant := (1595033874393134337265269738798777041903347370) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 40 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 40 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188501649696824618569/100000000000000000000)
  centralHi := (18850164969682461857/10000000000000000000)
  directionLo := (5965720044005912541/3125000000000000000)
  directionHi := (190903041408189201313/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree041.table
  base := (-96080009566205077346243885159610509457/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-61279130549186262169811256408660000000000000)
      constant := (817669529329194132245252139168540471037213360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree041.table
  base := (-240235518278531256619902608025609215499/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-123996866941389393099448578535320000000000000)
      constant := (1675444170496994910234052269627726849515806016) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 41 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 41 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5965720044005912541/3125000000000000000)
  centralHi := (190903041408189201313/100000000000000000000)
  directionLo := (193274598691522888013/100000000000000000000)
  directionHi := (96637299345761444007/50000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree042.table
  base := (-3860292393387975354859527666019823222619/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (943)
      previous := (0)
      next := (506)
      square := (17543973695327667802756899000000000000000)
      linear := (-995519625273065570311703525820000000000000)
      constant := (13617175235076547548725663789161502273950006) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree042.table
  base := (-7721519378181344377188970204206883856683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1260000000000000000000000000000000000000000
      center := (1909)
      previous := (0)
      next := (989)
      square := (35087947390655335605513798000000000000000)
      linear := (-2014431215473234697693749583640000000000000)
      constant := (27901811122639243135069644410309932634057942) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 42 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 42 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193274598691522888013/100000000000000000000)
  centralHi := (96637299345761444007/50000000000000000000)
  directionLo := (97808703319083063177/50000000000000000000)
  directionHi := (39123481327633225271/20000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree043.table
  base := (-7749626907844606255813322822735985253369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-64156342235219999689463387844660000000000000)
      constant := (899051194041811702940468108418220874529378439) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree043.table
  base := (-1937598878417030113171566856263100773087/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-129821466208238178809963869003320000000000000)
      constant := (1842142987204815245670771075130014024252941576) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 43 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 43 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97808703319083063177/50000000000000000000)
  centralHi := (39123481327633225271/20000000000000000000)
  directionLo := (197932486116640440931/100000000000000000000)
  directionHi := (49483121529160110233/25000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree044.table
  base := (-1554720352635884824446940676979214225727/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-65594948078236868449289453562660000000000000)
      constant := (941176695800128537762680271964627493690447685) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree044.table
  base := (-1554846708413083455651582194640911206087/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-132733765841662571665221514237320000000000000)
      constant := (1928430285777229893506845221061342234230406970) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 44 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 44 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (197932486116640440931/100000000000000000000)
  centralHi := (49483121529160110233/25000000000000000000)
  directionLo := (25027599871437707727/12500000000000000000)
  directionHi := (200220798971501661817/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree045.table
  base := (-7792569450790840878741063798498178610739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6601)
      previous := (0)
      next := (3542)
      square := (122807815867293674619298293000000000000000)
      linear := (-7448172657917081912123946586740000000000000)
      constant := (109362034061752175254553815122962303232664101) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree045.table
  base := (-7793088508337188874802304745192568536129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (13363)
      previous := (0)
      next := (6923)
      square := (245615631734587349238596586000000000000000)
      linear := (-15071785052787440502275462163480000000000000)
      constant := (224075062166288043777746500612540154551134222) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 45 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 45 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25027599871437707727/12500000000000000000)
  centralHi := (200220798971501661817/100000000000000000000)
  directionLo := (202483252693300294431/100000000000000000000)
  directionHi := (6327601646665634201/3125000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree046.table
  base := (-1951644594691976963756104961816296785617/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-68472159764270605968941584998660000000000000)
      constant := (1028295834177029376797832690198724472231544508) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree046.table
  base := (-3903502314037797278088439822391940061201/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-138558365108511357375736804705320000000000000)
      constant := (2106878457379532186515990641970465559588372924) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 46 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 46 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (202483252693300294431/100000000000000000000)
  centralHi := (6327601646665634201/3125000000000000000)
  directionLo := (102360352311980785991/50000000000000000000)
  directionHi := (204720704623961571983/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree047.table
  base := (-1953916888340757321707071644915137765323/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-69910765607287474728767650716660000000000000)
      constant := (1073289123848092143871559323013467272837732052) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree047.table
  base := (-3908008716190186009051413137820873366517/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-141470664741935750230994449939320000000000000)
      constant := (2199038697380179553227026819422275814433176108) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 47 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 47 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102360352311980785991/50000000000000000000)
  centralHi := (204720704623961571983/100000000000000000000)
  directionLo := (20693396575285493953/10000000000000000000)
  directionHi := (206933965752854939531/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree048.table
  base := (-3909934209128780107322738432893535429623/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6601)
      previous := (0)
      next := (3542)
      square := (122807815867293674619298293000000000000000)
      linear := (-7927707938922704832065968492740000000000000)
      constant := (124359783418776286706272028918827901751072514) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree048.table
  base := (-7820155486994011532416142206968026705669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (13363)
      previous := (0)
      next := (6923)
      square := (245615631734587349238596586000000000000000)
      linear := (-16042551597262238120694677241480000000000000)
      constant := (254795116971518956261665876573774200445599942) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 48 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 48 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20693396575285493953/10000000000000000000)
  centralHi := (206933965752854939531/100000000000000000000)
  directionLo := (52280951037804008779/25000000000000000000)
  directionHi := (209123804151216035117/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree049.table
  base := (-7819206333203878341334662147918250389753/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8487)
      previous := (0)
      next := (4554)
      square := (157895763257949010224812091000000000000000)
      linear := (-10398282470474458892631397450380000000000000)
      constant := (166591787755265071307121919287470352029010049) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree049.table
  base := (-3909720885172674167264867483884432375891/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11340000000000000000000000000000000000000000
      center := (17181)
      previous := (0)
      next := (8901)
      square := (315791526515898020449624182000000000000000)
      linear := (-21042180572683505134501391486760000000000000)
      constant := (341318620152462464543025884461470107371479212) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 49 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 49 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52280951037804008779/25000000000000000000)
  centralHi := (209123804151216035117/100000000000000000000)
  directionLo := (211290948086160522633/100000000000000000000)
  directionHi := (105645474043080261317/50000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree050.table
  base := (-7813701762871910999579783725573354824539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-74226583136338081008245847870660000000000000)
      constant := (1214002433177423958668352284224199354701404709) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree050.table
  base := (-7813894778288538316668433992917980386967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-150207563642208928796767385641320000000000000)
      constant := (2487261415530789200093111029567217071688255954) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 50 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 50 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211290948086160522633/100000000000000000000)
  centralHi := (105645474043080261317/50000000000000000000)
  directionLo := (213436088850084115861/100000000000000000000)
  directionHi := (106718044425042057931/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree051.table
  base := (-3901685616394907713146510003202110138749/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6601)
      previous := (0)
      next := (3542)
      square := (122807815867293674619298293000000000000000)
      linear := (-8407243219928327752007990398740000000000000)
      constant := (140313082427874522537626707978355738857623382) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree051.table
  base := (-7803529409827583360858003853930855814197/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (13363)
      previous := (0)
      next := (6923)
      square := (245615631734587349238596586000000000000000)
      linear := (-17013318141737035739113892319480000000000000)
      constant := (287472128651781409365695765000672985171878246) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 51 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 51 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (213436088850084115861/100000000000000000000)
  centralHi := (106718044425042057931/50000000000000000000)
  directionLo := (215559883336611177207/100000000000000000000)
  directionHi := (26944985417076397151/12500000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree052.table
  base := (-7788228098080041333395996285339847638963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-77103794822371818527897979306660000000000000)
      constant := (1312588387300714728754100766959726144720955853) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree052.table
  base := (-1947089419328364308486212105226374986351/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-156032162909057714507282676109320000000000000)
      constant := (2689193472718925674634407003625972141433383048) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 52 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 52 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (215559883336611177207/100000000000000000000)
  centralHi := (26944985417076397151/12500000000000000000)
  directionLo := (217662956390300462823/100000000000000000000)
  directionHi := (27207869548787557853/12500000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree053.table
  base := (-7768283161709080588232510976399361952483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-78542400665388687287724045024660000000000000)
      constant := (1363314326649982030193245933782530932410594973) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree053.table
  base := (-7768389275952183591286562977522236090149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-158944462542482107362540321343320000000000000)
      constant := (2793094283128922755346317794065108489916397238) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 53 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 53 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217662956390300462823/100000000000000000000)
  centralHi := (27207869548787557853/12500000000000000000)
  directionLo := (219745902953930545189/100000000000000000000)
  directionHi := (21974590295393054519/10000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree054.table
  base := (-7743545171755744365705585449783014559411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6601)
      previous := (0)
      next := (3542)
      square := (122807815867293674619298293000000000000000)
      linear := (-8886778500933950671950012304740000000000000)
      constant := (157221725019727533955876197828365690579299749) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree054.table
  base := (-1935908010134265277762498516303345665689/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (13363)
      previous := (0)
      next := (6923)
      square := (245615631734587349238596586000000000000000)
      linear := (-17984084686211833357533107397480000000000000)
      constant := (322105725211492746835522869830841796491449208) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 54 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 54 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (219745902953930545189/100000000000000000000)
  centralHi := (21974590295393054519/10000000000000000000)
  directionLo := (55452322508569625919/25000000000000000000)
  directionHi := (221809290034278503677/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree055.table
  base := (-7714021221409280654131382961236214260163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-81419612351422424807376176460660000000000000)
      constant := (1467631954730543929717393455015953465601413053) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree055.table
  base := (-482130769485764836050418589740276551559/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-164769061809330893073055611811320000000000000)
      constant := (3006765153709952049636180097305066955739594528) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 55 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 55 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55452322508569625919/25000000000000000000)
  centralHi := (221809290034278503677/100000000000000000000)
  directionLo := (2798170731309985587/1250000000000000000)
  directionHi := (223853658504798846961/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree056.table
  base := (-76797170707548244941248607524730947123/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8487)
      previous := (0)
      next := (4554)
      square := (157895763257949010224812091000000000000000)
      linear := (-11836888313491327652457463168380000000000000)
      constant := (217317656063884643080081170310307755298125900) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree056.table
  base := (-3839887615056335100304937253028990797031/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11340000000000000000000000000000000000000000
      center := (17181)
      previous := (0)
      next := (8901)
      square := (315791526515898020449624182000000000000000)
      linear := (-23954480206107897989759036720760000000000000)
      constant := (445219303249077612083380326814610248872333692) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 56 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 56 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2798170731309985587/1250000000000000000)
  centralHi := (223853658504798846961/100000000000000000000)
  directionLo := (45175904952288679601/20000000000000000000)
  directionHi := (112939762380721699003/50000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree057.table
  base := (-7640637405664820567371182255799077968061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6601)
      previous := (0)
      next := (3542)
      square := (122807815867293674619298293000000000000000)
      linear := (-9366313781939573591892034210740000000000000)
      constant := (175085602192140643132311286473452606616085099) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree057.table
  base := (-7640684971486991509250471840952769795967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (13363)
      previous := (0)
      next := (6923)
      square := (245615631734587349238596586000000000000000)
      linear := (-18954851230686630975952322475480000000000000)
      constant := (358695711206187438458587318426159657039957106) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 57 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 57 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45175904952288679601/20000000000000000000)
  centralHi := (112939762380721699003/50000000000000000000)
  directionLo := (11394369112299278721/5000000000000000000)
  directionHi := (227887382245985574421/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree058.table
  base := (-7596786046110888002702881442042188341773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-85735429880473031086854373614660000000000000)
      constant := (1631272421415296433285757285952494554471502963) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree058.table
  base := (-1899206234104691523901495795189280353711/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-173505960709604071638828547513320000000000000)
      constant := (3341943961053026976941189286394629970208968328) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 58 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 58 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11394369112299278721/5000000000000000000)
  centralHi := (227887382245985574421/100000000000000000000)
  directionLo := (229877702849581218817/100000000000000000000)
  directionHi := (114938851424790609409/50000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree059.table
  base := (-3774083056898225676459813408010985072631/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-87174035723489899846680439332660000000000000)
      constant := (1687729585115243544795373430950788800493455122) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree059.table
  base := (-188704947544429556885204381435996786367/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-176418260343028464494086192747320000000000000)
      constant := (3457582781292775760175093785061482300392750160) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 59 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 59 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229877702849581218817/100000000000000000000)
  centralHi := (114938851424790609409/50000000000000000000)
  directionLo := (231850938207876961851/100000000000000000000)
  directionHi := (57962734551969240463/25000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree060.table
  base := (-7494780167070239692179710686358622541823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6601)
      previous := (0)
      next := (3542)
      square := (122807815867293674619298293000000000000000)
      linear := (-9845849062945196511834056116740000000000000)
      constant := (193904655630557890780479527898115847459056057) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree060.table
  base := (-149896122851150689707052795355911712821/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (13363)
      previous := (0)
      next := (6923)
      square := (245615631734587349238596586000000000000000)
      linear := (-19925617775161428594371537553480000000000000)
      constant := (397241982612891183176723306105204293464593900) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 60 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 60 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231850938207876961851/100000000000000000000)
  centralHi := (57962734551969240463/25000000000000000000)
  directionLo := (2922594011221698527/1250000000000000000)
  directionHi := (233807520897735882161/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree061.table
  base := (-7436630309521259125220561999465420892307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-90051247409523637366332570768660000000000000)
      constant := (1803509359745484084742881390860941744478433517) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree061.table
  base := (-1859162882406168768989331181268219431599/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-182242859609877250204601483215320000000000000)
      constant := (3694729132871836444229025724721531496607868552) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 61 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 61 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2922594011221698527/1250000000000000000)
  centralHi := (233807520897735882161/100000000000000000000)
  directionLo := (117873932772281782887/50000000000000000000)
  directionHi := (9429914621782542631/4000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree062.table
  base := (-737371827740224353194844267285090362097/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-91489853252540506126158636486660000000000000)
      constant := (1862831955435445647181722396733894763528370070) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree062.table
  base := (-921716951022080137908675693613640221703/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-185155159243301643059859128449320000000000000)
      constant := (3816236637094441128939739215904479391360972688) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 62 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 62 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117873932772281782887/50000000000000000000)
  centralHi := (9429914621782542631/4000000000000000000)
  directionLo := (118836184924132053371/50000000000000000000)
  directionHi := (237672369848264106743/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree063.table
  base := (-3653022755010396489697436481048311316509/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (943)
      previous := (0)
      next := (506)
      square := (17543973695327667802756899000000000000000)
      linear := (-1475054906278688490253725431820000000000000)
      constant := (30525550508449108566266518489007912774119866) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree063.table
  base := (-7306059660743020930518056603464347458063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1260000000000000000000000000000000000000000
      center := (1909)
      previous := (0)
      next := (989)
      square := (35087947390655335605513798000000000000000)
      linear := (-2985197759948032316112964661640000000000000)
      constant := (62534926127033568734846619720523492220284062) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 63 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 63 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118836184924132053371/50000000000000000000)
  centralHi := (237672369848264106743/100000000000000000000)
  directionLo := (239581415535016950351/100000000000000000000)
  directionHi := (14973838470938559397/6250000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree064.table
  base := (-1446722641285431024669613982540890672629/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-94367064938574243645810767922660000000000000)
      constant := (1984342534776998229276262761628156024601677495) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree064.table
  base := (-1808406189444239785489363665335219385607/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-190979758510150428770374418917320000000000000)
      constant := (4065120251100600486586009548966116114068206536) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 64 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 64 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239581415535016950351/100000000000000000000)
  centralHi := (14973838470938559397/6250000000000000000)
  directionLo := (241475369241326311581/100000000000000000000)
  directionHi := (120737684620663155791/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree065.table
  base := (-286256894843044872873282936573216189771/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-95805670781591112405636833640660000000000000)
      constant := (2046530509682877747101641272873822623569972525) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree065.table
  base := (-3578215899146937844162097793280354256657/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-193892058143574821625632064151320000000000000)
      constant := (4192496345250513694242809637655281095821313468) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 65 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 65 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (241475369241326311581/100000000000000000000)
  centralHi := (120737684620663155791/50000000000000000000)
  directionLo := (24335458333614204061/10000000000000000000)
  directionHi := (243354583336142040611/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree066.table
  base := (-884309231327081572929076655715294910399/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6601)
      previous := (0)
      next := (3542)
      square := (122807815867293674619298293000000000000000)
      linear := (-10804919624956442351718099928740000000000000)
      constant := (234408178154398074762372159672516439556112328) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree066.table
  base := (-7074481542524250432087711520093273946977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (13363)
      previous := (0)
      next := (6923)
      square := (245615631734587349238596586000000000000000)
      linear := (-21867150864111023831209967709480000000000000)
      constant := (480203180268682767124161661791717732378766286) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 66 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 66 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24335458333614204061/10000000000000000000)
  centralHi := (243354583336142040611/100000000000000000000)
  directionLo := (61304849171568251939/25000000000000000000)
  directionHi := (245219396686273007757/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree067.table
  base := (-873471045442696255485683927359726506969/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-98682882467624849925288965076660000000000000)
      constant := (2173771813045414993514151935359013963950720312) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree067.table
  base := (-87347182976979559030397243460939326409/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-199716657410423607336147354619320000000000000)
      constant := (4453117077462128662860124682432085090157228640) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 67 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 67 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61304849171568251939/25000000000000000000)
  centralHi := (245219396686273007757/100000000000000000000)
  directionLo := (247070135369801708857/100000000000000000000)
  directionHi := (123535067684900854429/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree068.table
  base := (-6896306524090887335231832738421377443039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-100121488310641718685115030794660000000000000)
      constant := (2238825136212456096938977305303365552928578209) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree068.table
  base := (-6896311641448600266442049353708264500711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-202628957043848000191404999853320000000000000)
      constant := (4586361705966933564479972927694343796393356082) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 68 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 68 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (247070135369801708857/100000000000000000000)
  centralHi := (123535067684900854429/50000000000000000000)
  directionLo := (248907113341753576769/100000000000000000000)
  directionHi := (24890711334175357677/10000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree069.table
  base := (-53125694230702016417156921544968507639/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6601)
      previous := (0)
      next := (3542)
      square := (122807815867293674619298293000000000000000)
      linear := (-11284454905962065271660121834740000000000000)
      constant := (256092618976672465713676627547049617680793728) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree069.table
  base := (-6800093034184468343855812522381618462399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (13363)
      previous := (0)
      next := (6923)
      square := (245615631734587349238596586000000000000000)
      linear := (-22837917408585821449629182787480000000000000)
      constant := (524618056012012718715382785889219412516164082) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 69 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 69 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (248907113341753576769/100000000000000000000)
  centralHi := (24890711334175357677/10000000000000000000)
  directionLo := (250730633055869305041/100000000000000000000)
  directionHi := (125365316527934652521/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree070.table
  base := (-2143717067425182075192797862776322859/3200000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8487)
      previous := (0)
      next := (4554)
      square := (157895763257949010224812091000000000000000)
      linear := (-14714099999525065172109594604380000000000000)
      constant := (338828159279011090279573213053093202934209375) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree070.table
  base := (-1339823847470942754971516409901789761669/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11340000000000000000000000000000000000000000
      center := (17181)
      previous := (0)
      next := (8901)
      square := (315791526515898020449624182000000000000000)
      linear := (-29779079472956683700274327188760000000000000)
      constant := (694102781220551816907559493376456852051336770) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 70 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 70 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (250730633055869305041/100000000000000000000)
  centralHi := (125365316527934652521/50000000000000000000)
  directionLo := (252540986045967202841/100000000000000000000)
  directionHi := (126270493022983601421/50000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree071.table
  base := (-6593387849594627121570961795812853741589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-104437305839692324964593227948660000000000000)
      constant := (2439715767102095939194569649895438783499633259) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree071.table
  base := (-3296695311074888383945860325569861413199/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-211365855944121178757177935555320000000000000)
      constant := (4997832596327668599848755718351012880204052676) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 71 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 71 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252540986045967202841/100000000000000000000)
  centralHi := (126270493022983601421/50000000000000000000)
  directionLo := (508676906940119787/200000000000000000)
  directionHi := (254338453470059893501/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree072.table
  base := (-1620726314866302473601500094741737204031/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6601)
      previous := (0)
      next := (3542)
      square := (122807815867293674619298293000000000000000)
      linear := (-11763990186967688191602143740740000000000000)
      constant := (278732169535900115858524800253835575572089316) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree072.table
  base := (-6482907518828721175580644681365766823841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (13363)
      previous := (0)
      next := (6923)
      square := (245615631734587349238596586000000000000000)
      linear := (-23808683953060619068048397865480000000000000)
      constant := (570989098315326184895982902903515393661372238) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 72 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 72 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (508676906940119787/200000000000000000)
  centralHi := (254338453470059893501/100000000000000000000)
  directionLo := (256123306620100939033/100000000000000000000)
  directionHi := (128061653310050469517/50000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree073.table
  base := (-6367668383057690116878030205320870804067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-107314517525726062484245359384660000000000000)
      constant := (2578418389854973960982106722055341463778658077) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree073.table
  base := (-1273534044774226436470787425337725334623/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-217190455210969964467693226023320000000000000)
      constant := (5281927331721208963804185647230225681468813130) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 73 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 73 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (256123306620100939033/100000000000000000000)
  centralHi := (128061653310050469517/50000000000000000000)
  directionLo := (51579161479995644273/20000000000000000000)
  directionHi := (128947903699989110683/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree074.table
  base := (-249907100249101958024875416580392830677/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-108753123368742931244071425102660000000000000)
      constant := (2649202358063154289230191552507690521376074675) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree074.table
  base := (-78095987571892314424383500381667444527/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-220102754844394357322950871257320000000000000)
      constant := (5426908934846338907416537448386065906027573920) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 74 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 74 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51579161479995644273/20000000000000000000)
  centralHi := (128947903699989110683/50000000000000000000)
  directionLo := (259656208774138658269/100000000000000000000)
  directionHi := (25965620877413865827/10000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree075.table
  base := (-1224586577663095317416142410288336017111/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6601)
      previous := (0)
      next := (3542)
      square := (122807815867293674619298293000000000000000)
      linear := (-12243525467973311111544165646740000000000000)
      constant := (302326825490924314233459982998814219082270245) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree075.table
  base := (-122458682192120589274878888400375661521/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (13363)
      previous := (0)
      next := (6923)
      square := (245615631734587349238596586000000000000000)
      linear := (-24779450497535416686467612943480000000000000)
      constant := (619316299140825729552785121309543433326923900) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 75 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 75 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259656208774138658269/100000000000000000000)
  centralHi := (25965620877413865827/10000000000000000000)
  directionLo := (52280951037804008779/20000000000000000000)
  directionHi := (32675594398627505487/12500000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree076.table
  base := (-5993434766502677182802400639328848020189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-111630335054776668763723556538660000000000000)
      constant := (2793635602979095378297613028013623802207869859) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree076.table
  base := (-5993435761011560560871173481860930388247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-225927354111243143033466161725320000000000000)
      constant := (5722740602193860718604518553413547934578095314) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 76 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 76 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52280951037804008779/20000000000000000000)
  centralHi := (32675594398627505487/12500000000000000000)
  directionLo := (65785420742319457321/25000000000000000000)
  directionHi := (52628336593855565857/20000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree077.table
  base := (-1171836671869323427466673496487770355903/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8487)
      previous := (0)
      next := (4554)
      square := (157895763257949010224812091000000000000000)
      linear := (-16152705842541933931935660322380000000000000)
      constant := (409612125411147050811401624181277171041014995) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree077.table
  base := (-366199010565434969897675759284004885859/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11340000000000000000000000000000000000000000
      center := (17181)
      previous := (0)
      next := (8901)
      square := (315791526515898020449624182000000000000000)
      linear := (-32691379106381076555531972422760000000000000)
      constant := (839084380423708201935311308770711015350974304) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 77 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 77 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65785420742319457321/25000000000000000000)
  centralHi := (52628336593855565857/20000000000000000000)
  directionLo := (4138550323291018383/1562500000000000000)
  directionHi := (264867220690625176513/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree078.table
  base := (-357511179353493092712202389317073502563/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6601)
      previous := (0)
      next := (3542)
      square := (122807815867293674619298293000000000000000)
      linear := (-12723060748978934031486187552740000000000000)
      constant := (326876583701130383833429193173018729365915472) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree078.table
  base := (-1430044882195242045473387649440843609927/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (13363)
      previous := (0)
      next := (6923)
      square := (245615631734587349238596586000000000000000)
      linear := (-25750217042010214304886828021480000000000000)
      constant := (669599652559473997559120247233292703744177544) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 78 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 78 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4138550323291018383/1562500000000000000)
  centralHi := (264867220690625176513/100000000000000000000)
  directionLo := (66645397382737899027/25000000000000000000)
  directionHi := (266581589530951596109/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree079.table
  base := (-5576421486831936162029979919004007171089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-115946152583827275043201753692660000000000000)
      constant := (3017448728523793351696771568697453095537947759) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree079.table
  base := (-697052752912057612601146889088459076741/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-234664253011516321599239097427320000000000000)
      constant := (6181159230948474555474120893011566494790639536) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 79 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 79 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66645397382737899027/25000000000000000000)
  centralHi := (266581589530951596109/100000000000000000000)
  directionLo := (268285003601247122797/100000000000000000000)
  directionHi := (134142501800623561399/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree080.table
  base := (-5427911388780480791590495383881821022757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-117384758426844143803027819410660000000000000)
      constant := (3093963302812781230226295188350973052360677467) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree080.table
  base := (-5427911825342124222093970174277130316153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-237576552644940714454496742661320000000000000)
      constant := (6337877735334304072063333914921388139550377486) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 80 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 80 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268285003601247122797/100000000000000000000)
  centralHi := (134142501800623561399/50000000000000000000)
  directionLo := (269977670257733725909/100000000000000000000)
  directionHi := (26997767025773372591/10000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree081.table
  base := (-164832773233609250881051765653065600927/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6601)
      previous := (0)
      next := (3542)
      square := (122807815867293674619298293000000000000000)
      linear := (-13202596029984556951428209458740000000000000)
      constant := (352381441723383154735256192559683938239718176) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree081.table
  base := (-1054929819736776805115186517358516197933/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (13363)
      previous := (0)
      next := (6923)
      square := (245615631734587349238596586000000000000000)
      linear := (-26720983586485011923306043099480000000000000)
      constant := (721839153876975623129516294688488943567115470) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 81 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 81 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269977670257733725909/100000000000000000000)
  centralHi := (26997767025773372591/10000000000000000000)
  directionLo := (271659790396492100529/100000000000000000000)
  directionHi := (27165979039649210053/10000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree082.table
  base := (-1279158427560602908911916829102299106481/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-120261970112877881322679950846660000000000000)
      constant := (3249857745984432208137248440896011899385507644) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree082.table
  base := (-2558316999607129658482136681309186390713/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-243401151911789500165012033129320000000000000)
      constant := (6657183178386429347913739387820455356861040412) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 82 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 82 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (271659790396492100529/100000000000000000000)
  centralHi := (27165979039649210053/10000000000000000000)
  directionLo := (273331558731768918493/100000000000000000000)
  directionHi := (136665779365884459247/50000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree083.table
  base := (-619233305101787205749464426039429732279/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-121700575955894750082506016564660000000000000)
      constant := (3329237613632504121828943900430856027140677192) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree083.table
  base := (-2476933337933189325005637240889459906707/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-246313451545213893020269678363320000000000000)
      constant := (6819770114633019116847926507436118934521119668) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 83 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 83 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273331558731768918493/100000000000000000000)
  centralHi := (136665779365884459247/50000000000000000000)
  directionLo := (137496582029527975583/50000000000000000000)
  directionHi := (274993164059055951167/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree084.table
  base := (-2393173540102158336418067040734472340367/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (943)
      previous := (0)
      next := (506)
      square := (17543973695327667802756899000000000000000)
      linear := (-1954590187284311410195747337820000000000000)
      constant := (54120199648874712559984449631027456485113758) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree084.table
  base := (-478634727137021177647929639255886466567/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1260000000000000000000000000000000000000000
      center := (1909)
      previous := (0)
      next := (989)
      square := (35087947390655335605513798000000000000000)
      linear := (-3955964304422829934532179739640000000000000)
      constant := (110862114166659673255217752282617583052125580) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 84 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 84 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137496582029527975583/50000000000000000000)
  centralHi := (274993164059055951167/100000000000000000000)
  directionLo := (11065791580157889943/4000000000000000000)
  directionHi := (4322574835999175759/1562500000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree085.table
  base := (-2307037883714667966268932564025548382393/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-124577787641928487602158148000660000000000000)
      constant := (3490862638172482570505709389894465196940564366) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree085.table
  base := (-144189872590037460487431077597119668577/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-252138050812062678730784968831320000000000000)
      constant := (7150812410897310359574711630055690050266744768) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 85 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 85 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11065791580157889943/4000000000000000000)
  centralHi := (4322574835999175759/1562500000000000000)
  directionLo := (69571653189425730081/25000000000000000000)
  directionHi := (11131464510308116813/4000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree086.table
  base := (-1109263159028206231699198273260756324349/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-126016393484945356361984213718660000000000000)
      constant := (3573107793982279609056780124091032232594635276) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree086.table
  base := (-443705276250554273259834823627658789653/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-255050350445487071586042614065320000000000000)
      constant := (7319267768777612909292777938253596445277344860) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 86 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 86 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69571653189425730081/25000000000000000000)
  centralHi := (11131464510308116813/4000000000000000000)
  directionLo := (27991880630037725601/10000000000000000000)
  directionHi := (279918806300377256011/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree087.table
  base := (-4255277814989718921547243673994623877273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6601)
      previous := (0)
      next := (3542)
      square := (122807815867293674619298293000000000000000)
      linear := (-14161666591995802791312253270740000000000000)
      constant := (406256449421949894317971021183428370870122607) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree087.table
  base := (-212763895887084213959427729419593177473/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (13363)
      previous := (0)
      next := (6923)
      square := (245615631734587349238596586000000000000000)
      linear := (-28662516675434607160144473255480000000000000)
      constant := (832186585014264938161220268213118376349376280) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 87 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 87 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27991880630037725601/10000000000000000000)
  centralHi := (279918806300377256011/100000000000000000000)
  directionLo := (8798173050384508541/3125000000000000000)
  directionHi := (281541537612304273313/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree088.table
  base := (-813750285666308754210737832350225577441/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-128893605170979093881636345154660000000000000)
      constant := (3740463390125057203805010899051569773415683355) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree088.table
  base := (-4068751511853661520747964730432441371949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-260874949712335857296557904533320000000000000)
      constant := (7662046898971155027251302179695107280389468838) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 88 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 88 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8798173050384508541/3125000000000000000)
  centralHi := (281541537612304273313/100000000000000000000)
  directionLo := (283154969374674690409/100000000000000000000)
  directionHi := (28315496937467469041/10000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree089.table
  base := (-60585524942290110411849561353085652071/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-130332211013995962641462410872660000000000000)
      constant := (3825573829487856219817748589325514595003532864) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree089.table
  base := (-1938736832094500211942385156559186280031/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-263787249345760250151815549767320000000000000)
      constant := (7836370669358543999570801410261306358618227844) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 89 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 89 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (283154969374674690409/100000000000000000000)
  centralHi := (28315496937467469041/10000000000000000000)
  directionLo := (17797453728742765659/6250000000000000000)
  directionHi := (56951851931976850109/20000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree090.table
  base := (-3681444435286897311340036997735834921577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6601)
      previous := (0)
      next := (3542)
      square := (122807815867293674619298293000000000000000)
      linear := (-14641201873001425711254275176740000000000000)
      constant := (434626595824896133138673058050198496799584543) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree090.table
  base := (-92036112261283002695657492169956492521/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (13363)
      previous := (0)
      next := (6923)
      square := (245615631734587349238596586000000000000000)
      linear := (-29633283219909404778563688333480000000000000)
      constant := (890294508374677336871228174796843934943859120) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 90 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 90 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17797453728742765659/6250000000000000000)
  centralHi := (56951851931976850109/20000000000000000000)
  directionLo := (286354562112283801969/100000000000000000000)
  directionHi := (28635456211228380197/10000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree091.table
  base := (-3480664058112162701001907706196375306971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8487)
      previous := (0)
      next := (4554)
      square := (157895763257949010224812091000000000000000)
      linear := (-19029917528575671451587791758380000000000000)
      constant := (571237141212260522112852843575646655200947443) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree091.table
  base := (-870166025733965998143380201416188554367/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11340000000000000000000000000000000000000000
      center := (17181)
      previous := (0)
      next := (8901)
      square := (315791526515898020449624182000000000000000)
      linear := (-38515978373229862266047262890760000000000000)
      constant := (1170126659445773068827727283543656168717391288) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 91 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 91 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286354562112283801969/100000000000000000000)
  centralHi := (28635456211228380197/10000000000000000000)
  directionLo := (287941026119916128041/100000000000000000000)
  directionHi := (143970513059958064021/50000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree092.table
  base := (-3275132574317556156934234696627347908453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-134648028543046568920940608026660000000000000)
      constant := (4086635707238386408737694032250126056151350043) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree092.table
  base := (-32751326107345810711725973053274824661/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-272524148246033428717588485469320000000000000)
      constant := (8371078790737518458323113198223830444184098200) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 92 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 92 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (287941026119916128041/100000000000000000000)
  centralHi := (143970513059958064021/50000000000000000000)
  directionLo := (289518796977782846547/100000000000000000000)
  directionHi := (72379699244445711637/25000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree093.table
  base := (-3064850090332546710900358507585524155711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6601)
      previous := (0)
      next := (3542)
      square := (122807815867293674619298293000000000000000)
      linear := (-15120737154007048631196297082740000000000000)
      constant := (463951835362148321944906800612894783847331449) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree093.table
  base := (-3064850119916106846255399028716365387633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (13363)
      previous := (0)
      next := (6923)
      square := (245615631734587349238596586000000000000000)
      linear := (-30604049764384202396982903411480000000000000)
      constant := (950358566486827125867580936734792165728107694) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 93 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 93 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (289518796977782846547/100000000000000000000)
  centralHi := (72379699244445711637/25000000000000000000)
  directionLo := (291088016043146410291/100000000000000000000)
  directionHi := (72772004010786602573/25000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree094.table
  base := (-2849816709655359230314013550745604673911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-137525240229080306440592739462660000000000000)
      constant := (4265452421137884666590606312947370695049247241) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree094.table
  base := (-1424908366842484403846218537360048930037/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-278348747512882214428103775937320000000000000)
      constant := (8737331538232950966034844564870511863186732588) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 94 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 94 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291088016043146410291/100000000000000000000)
  centralHi := (72772004010786602573/25000000000000000000)
  directionLo := (146324410441668516877/50000000000000000000)
  directionHi := (58529764176667406751/20000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree095.table
  base := (-2630032533007358608807578233111225382003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-138963846072097175200418805180660000000000000)
      constant := (4356293415474272618734202444646681546458830093) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree095.table
  base := (-2630032552523517428912232668190212609067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-281261047146306607283361421171320000000000000)
      constant := (8923392109494410059944885999513106092309226154) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 95 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 95 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (146324410441668516877/50000000000000000000)
  centralHi := (58529764176667406751/20000000000000000000)
  directionLo := (294201345416501965361/100000000000000000000)
  directionHi := (147100672708250982681/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree096.table
  base := (-300687207308836955358647400159156948659/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6601)
      previous := (0)
      next := (3542)
      square := (122807815867293674619298293000000000000000)
      linear := (-15600272435012671551138318988740000000000000)
      constant := (494232166764356744158187580661518494285131048) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree096.table
  base := (-481099534863884187064128182656002466611/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (13363)
      previous := (0)
      next := (6923)
      square := (245615631734587349238596586000000000000000)
      linear := (-31574816308859000015402118489480000000000000)
      constant := (1012378756820976567129453450747127029122245490) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 96 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 96 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (294201345416501965361/100000000000000000000)
  centralHi := (147100672708250982681/50000000000000000000)
  directionLo := (18484107502856541973/6250000000000000000)
  directionHi := (295745720045704671569/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree097.table
  base := (-435242436322388691847084558264439668443/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-141841057758130912720070936616660000000000000)
      constant := (4540840676973395173919046066320382194779748665) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree097.table
  base := (-544053048620257195695746373273089753053/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-287085646413155392993876711639320000000000000)
      constant := (9301381643158736620714770797107152854161061144) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 97 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 97 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18484107502856541973/6250000000000000000)
  centralHi := (295745720045704671569/100000000000000000000)
  directionLo := (29728207178675397213/10000000000000000000)
  directionHi := (297282071786753972131/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree098.table
  base := (-1942176195593946234810462531917395101113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8487)
      previous := (0)
      next := (4554)
      square := (157895763257949010224812091000000000000000)
      linear := (-20468523371592540211413857476380000000000000)
      constant := (662078134769580388526020482913082836977668929) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree098.table
  base := (-1942176206042479386597940406808519774431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11340000000000000000000000000000000000000000
      center := (17181)
      previous := (0)
      next := (8901)
      square := (315791526515898020449624182000000000000000)
      linear := (-41428278006654255121304908124760000000000000)
      constant := (1356187229152249659836187763779519138575795246) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 98 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 98 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29728207178675397213/10000000000000000000)
  centralHi := (297282071786753972131/100000000000000000000)
  directionLo := (59762104878023552441/20000000000000000000)
  directionHi := (149405262195058881103/50000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree099.table
  base := (-1703389791277692469441649682385261315291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6601)
      previous := (0)
      next := (3542)
      square := (122807815867293674619298293000000000000000)
      linear := (-16079807716018294471080340894740000000000000)
      constant := (525467588862176230150787336779888099759956669) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree099.table
  base := (-340677959952016341148165844857287981347/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (13363)
      previous := (0)
      next := (6923)
      square := (245615631734587349238596586000000000000000)
      linear := (-32545582853333797633821333567480000000000000)
      constant := (1076355077043266502007151731808339360002259730) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 99 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 99 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59762104878023552441/20000000000000000000)
  centralHi := (149405262195058881103/50000000000000000000)
  directionLo := (75082799614313123181/25000000000000000000)
  directionHi := (12013247938290099709/4000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree100.table
  base := (-72992652865784712167191467314584258509/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-146156875287181518999549133770660000000000000)
      constant := (4824824745739103408497501297986568301559555580) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree100.table
  base := (-729926532100610698362382418367978005417/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-295822545313428571559649647341320000000000000)
      constant := (9883036910426641411006523426431989981185999708) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 100 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 100 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75082799614313123181/25000000000000000000)
  centralHi := (12013247938290099709/4000000000000000000)
  directionLo := (301844211551657889477/100000000000000000000)
  directionHi := (150922105775828944739/50000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree101.table
  base := (-302891520059521607780299800356336114669/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-147595481130198387759375199488660000000000000)
      constant := (4921396280982176625786085120711162807843514956) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree101.table
  base := (-121156608582681723056628279336591616037/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-298734844946852964414907292575320000000000000)
      constant := (10080834254491149524475458607737821357518982940) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 101 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 101 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (301844211551657889477/100000000000000000000)
  centralHi := (150922105775828944739/50000000000000000000)
  directionLo := (75837419576236580847/25000000000000000000)
  directionHi := (303349678304946323389/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree102.table
  base := (-958528944532443449572861967892851280021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6601)
      previous := (0)
      next := (3542)
      square := (122807815867293674619298293000000000000000)
      linear := (-16559342997023917391022362800740000000000000)
      constant := (557658100572608282262506873388519252585510739) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree102.table
  base := (-958528949068171739441738313929368723451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (13363)
      previous := (0)
      next := (6923)
      square := (245615631734587349238596586000000000000000)
      linear := (-33516349397808595252240548645480000000000000)
      constant := (1142287524990300797663417246939794296785916218) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 102 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 102 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75837419576236580847/25000000000000000000)
  centralHi := (303349678304946323389/100000000000000000000)
  directionLo := (304847710518197663121/100000000000000000000)
  directionHi := (152423855259098831561/50000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree103.table
  base := (-140148346543627176426108669482975764933/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-150472692816232125279027330924660000000000000)
      constant := (5117404617925477770381290998032970345944904615) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree103.table
  base := (-700741736398913137646582807374929074653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-304559444213701750125422583043320000000000000)
      constant := (10482297321036638713727335977308737813005404486) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 103 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 103 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (304847710518197663121/100000000000000000000)
  centralHi := (152423855259098831561/50000000000000000000)
  directionLo := (76584604314713305727/25000000000000000000)
  directionHi := (306338417258853222909/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree104.table
  base := (-438204525415907274506522725666256596751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-151911298659248994038853396642660000000000000)
      constant := (5216841418978202584709340496438310627567495281) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree104.table
  base := (-87640905680521325871118292900916093901/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-307471743847126142980680228277320000000000000)
      constant := (10685963042223271788154461506825002640233069310) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 104 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 104 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76584604314713305727/25000000000000000000)
  centralHi := (306338417258853222909/100000000000000000000)
  directionLo := (76955476238346612779/25000000000000000000)
  directionHi := (307821904953386451117/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree105.table
  base := (-273467842261177781031336656355329081/16000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (943)
      previous := (0)
      next := (506)
      square := (17543973695327667802756899000000000000000)
      linear := (-2434125468289934330137769243820000000000000)
      constant := (84400528698395896527524047171856008917435625) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree105.table
  base := (-170917403836516801697140270272244816617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1260000000000000000000000000000000000000000
      center := (1909)
      previous := (0)
      next := (989)
      square := (35087947390655335605513798000000000000000)
      linear := (-4926730848897627552951394817640000000000000)
      constant := (172882299807102083110468361308545697153106258) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 105 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 105 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76955476238346612779/25000000000000000000)
  centralHi := (307821904953386451117/100000000000000000000)
  directionLo := (154649138737986593249/50000000000000000000)
  directionHi := (309298277475973186499/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree106.table
  base := (101119562274045689992745152355368635893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-154788510345282731558505528078660000000000000)
      constant := (5418580284682018623096735168639418458115859317) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree106.table
  base := (101119560308075487880333129458482283349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-313296343113974928691195518745320000000000000)
      constant := (11099162857297960269696046046116001432365224362) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 106 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 106 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (154649138737986593249/50000000000000000000)
  centralHi := (309298277475973186499/100000000000000000000)
  directionLo := (310767636233370546599/100000000000000000000)
  directionHi := (1553838181166852733/500000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree107.table
  base := (94476572585870685019739246992795244071/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-156227116188299600318331593796660000000000000)
      constant := (5520882348728558564835434660850597617294871196) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree107.table
  base := (94476572187165503705266417107167593787/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-316208642747399321546453163979320000000000000)
      constant := (11308696949977266339077555710637906785437924824) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 107 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 107 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (310767636233370546599/100000000000000000000)
  centralHi := (1553838181166852733/500000000000000000)
  directionLo := (312230080246200721871/100000000000000000000)
  directionHi := (19514380015387545117/6250000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree108.table
  base := (329721354575370821968854536270464349051/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6601)
      previous := (0)
      next := (3542)
      square := (122807815867293674619298293000000000000000)
      linear := (-17518413559035163230906406612740000000000000)
      constant := (624904388871807438579177394548430549555862982) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree108.table
  base := (659442707857114098685420476293091377717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (13363)
      previous := (0)
      next := (6923)
      square := (245615631734587349238596586000000000000000)
      linear := (-35457882486758190489078978801480000000000000)
      constant := (1280020796144543262070967324280810506595146394) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 108 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 108 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312230080246200721871/100000000000000000000)
  centralHi := (19514380015387545117/6250000000000000000)
  directionLo := (156842853113412026337/50000000000000000000)
  directionHi := (12547428249072962107/4000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree109.table
  base := (236432186664272489233254822302253226011/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-159104327874333337837983725232660000000000000)
      constant := (5728351737749222041155460625873450572216150636) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree109.table
  base := (945728745607862188320018283515653461297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-322033242014248107256968454447320000000000000)
      constant := (11733633502697090357282441145142587257175775586) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 109 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 109 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156842853113412026337/50000000000000000000)
  centralHi := (12547428249072962107/4000000000000000000)
  directionLo := (157567304326987347139/50000000000000000000)
  directionHi := (315134608653974694279/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree110.table
  base := (1236764332379368121644256232195619526359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-160542933717350206597809790950660000000000000)
      constant := (5833519062157676186380624399613784413900118871) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree110.table
  base := (1236764331528437581388359921043598086273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-324945541647672500112226099681320000000000000)
      constant := (11949035961606458878449614260079844081608835074) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 110 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 110 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157567304326987347139/50000000000000000000)
  centralHi := (315134608653974694279/100000000000000000000)
  directionLo := (158288439922160931549/50000000000000000000)
  directionHi := (316576879844321863099/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree111.table
  base := (76627469867112404711437377660292869291/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6601)
      previous := (0)
      next := (3542)
      square := (122807815867293674619298293000000000000000)
      linear := (-17997948840040786150848428518740000000000000)
      constant := (659960163644207367320230700622943783107146620) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree111.table
  base := (191568674581524293766992009935885840611/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (13363)
      previous := (0)
      next := (6923)
      square := (245615631734587349238596586000000000000000)
      linear := (-36428649031232988107498193879480000000000000)
      constant := (1351821615720170854085078885382347610491351216) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 111 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 111 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158288439922160931549/50000000000000000000)
  centralHi := (316576879844321863099/100000000000000000000)
  directionLo := (79503152505277511761/25000000000000000000)
  directionHi := (63602522004222009409/20000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree112.table
  base := (1833083874032600493087381543623644458977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8487)
      previous := (0)
      next := (4554)
      square := (157895763257949010224812091000000000000000)
      linear := (-23345735057626277731065988912380000000000000)
      constant := (863816995628833255592035638497154606408239959) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree112.table
  base := (1833083873473053156478088663830493831513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11340000000000000000000000000000000000000000
      center := (17181)
      previous := (0)
      next := (8901)
      square := (315791526515898020449624182000000000000000)
      linear := (-47252877273503040831820198592760000000000000)
      constant := (1769387034540923360635001750609743780004935742) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 112 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 112 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79503152505277511761/25000000000000000000)
  centralHi := (63602522004222009409/20000000000000000000)
  directionLo := (79860471845005650117/25000000000000000000)
  directionHi := (319441887380022600469/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree113.table
  base := (534591924088953839040457787767353076243/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-164858751246400812877287988104660000000000000)
      constant := (6154751551707246129227734391163654497438433868) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree113.table
  base := (133647980993883012618615484610197767263/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-333682440547945678677999035383320000000000000)
      constant := (12606980061996622816018893410333651998024539104) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 113 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 113 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79860471845005650117/25000000000000000000)
  centralHi := (319441887380022600469/100000000000000000000)
  directionLo := (8021619953810119517/2500000000000000000)
  directionHi := (320864798152404780681/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree114.table
  base := (1224200399796970439063706138319017156429/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6601)
      previous := (0)
      next := (3542)
      square := (122807815867293674619298293000000000000000)
      linear := (-18477484121046409070790450424740000000000000)
      constant := (695971024384137863935244155496517373131970378) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree114.table
  base := (1224200399613057418419404727947287230739/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (13363)
      previous := (0)
      next := (6923)
      square := (245615631734587349238596586000000000000000)
      linear := (-37399415575707785725917408957480000000000000)
      constant := (1425578555733146816575463855836859014675023596) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 114 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 114 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8021619953810119517/2500000000000000000)
  centralHi := (320864798152404780681/100000000000000000000)
  directionLo := (322281426665974473401/100000000000000000000)
  directionHi := (161140713332987236701/50000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree115.table
  base := (2763183120365520559470089261555116232831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-167735962932434550396940119540660000000000000)
      constant := (6373681972400255726866067286865412256328106239) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree115.table
  base := (2763183120067328966634704252509348597849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-339507039814794464388514325851320000000000000)
      constant := (13055390060088467067582395283430819209169725362) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 115 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 115 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (322281426665974473401/100000000000000000000)
  centralHi := (161140713332987236701/50000000000000000000)
  directionLo := (64738371080628311527/20000000000000000000)
  directionHi := (80922963850785389409/25000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree116.table
  base := (3082714596587022635504503021305890297619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-169174568775451419156766185258660000000000000)
      constant := (6484579810289881446000307863147483078591249811) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree116.table
  base := (123308583853812033323524156965061017801/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-342419339448218857243771971085320000000000000)
      constant := (13282529236974265202287983967824676358982608450) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 116 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 116 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64738371080628311527/20000000000000000000)
  centralHi := (80922963850785389409/25000000000000000000)
  directionLo := (65019233011410007687/20000000000000000000)
  directionHi := (81274041264262509609/25000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree117.table
  base := (851748791858941737265764262875724054241/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6601)
      previous := (0)
      next := (3542)
      square := (122807815867293674619298293000000000000000)
      linear := (-18957019402052031990732472330740000000000000)
      constant := (732936970320523635030680104198772777231681124) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree117.table
  base := (3406995167239835422817104327709443545429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (13363)
      previous := (0)
      next := (6923)
      square := (245615631734587349238596586000000000000000)
      linear := (-38370182120182583344336624035480000000000000)
      constant := (1501291614641436116142190577847319729207068378) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 117 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 117 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65019233011410007687/20000000000000000000)
  centralHi := (81274041264262509609/25000000000000000000)
  directionLo := (65298886917090138847/20000000000000000000)
  directionHi := (81623608646362673559/25000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree118.table
  base := (3736024773314263977330143131166943087227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-172051780461485156676418316694660000000000000)
      constant := (6709240739948207098777451361760761597113203963) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree118.table
  base := (3736024773155459978342439484325140821609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-348243938715067642954287261553320000000000000)
      constant := (13742675944011377733808718568493652967841932242) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 118 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 118 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65298886917090138847/20000000000000000000)
  centralHi := (81623608646362673559/25000000000000000000)
  directionLo := (327886741262506011783/100000000000000000000)
  directionHi := (40985842657813251473/12500000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree119.table
  base := (2034901677907944418791131830604833164703/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8487)
      previous := (0)
      next := (4554)
      square := (157895763257949010224812091000000000000000)
      linear := (-24784340900643146490892054630380000000000000)
      constant := (974714833035506957477824224727445880808773202) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree119.table
  base := (127181354865224566442176982341177855413/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 11340000000000000000000000000000000000000000
      center := (17181)
      previous := (0)
      next := (8901)
      square := (315791526515898020449624182000000000000000)
      linear := (-50165176906927433687077843826760000000000000)
      constant := (1996526210460857781452290914200716662017226944) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 119 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 119 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327886741262506011783/100000000000000000000)
  centralHi := (40985842657813251473/12500000000000000000)
  directionLo := (329273160728623587103/100000000000000000000)
  directionHi := (10289786272769487097/3125000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree120.table
  base := (2204165428845910017437090253287478528287/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6601)
      previous := (0)
      next := (3542)
      square := (122807815867293674619298293000000000000000)
      linear := (-19436554683057654910674494236740000000000000)
      constant := (770858000728724105940515324624999556061949134) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree120.table
  base := (27552067859922001240582011780302766331/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (13363)
      previous := (0)
      next := (6923)
      square := (245615631734587349238596586000000000000000)
      linear := (-39340948664657380962755839113480000000000000)
      constant := (1578960790995819405513011521063236326384630720) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 120 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 120 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (329273160728623587103/100000000000000000000)
  centralHi := (10289786272769487097/3125000000000000000)
  directionLo := (66130753407681785613/20000000000000000000)
  directionHi := (165326883519204464033/50000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree121.table
  base := (4751607222819178684368608598841606187073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-176367597990535762955896513848660000000000000)
      constant := (7053395265655360145843137222922822334956492737) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree121.table
  base := (4751607222734660582730867701308644450621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-356980837615340821520060197255320000000000000)
      constant := (14447566880774993410960768662645748019649029498) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 121 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 121 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66130753407681785613/20000000000000000000)
  centralHi := (165326883519204464033/50000000000000000000)
  directionLo := (41503579088352959803/12500000000000000000)
  directionHi := (13281145308272947137/4000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree122.table
  base := (5099632396170309110653903460569266960637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-177806203833552631715722579566660000000000000)
      constant := (7170023608320673514104558660054639420566768253) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree122.table
  base := (101992647922036510436249585920914963841/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-359893137248765214375317842489320000000000000)
      constant := (14686442758227058160609565072067331149148492900) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 122 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 122 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41503579088352959803/12500000000000000000)
  centralHi := (13281145308272947137/4000000000000000000)
  directionLo := (333397828753630671489/100000000000000000000)
  directionHi := (33339782875363067149/10000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree123.table
  base := (1090481264756629246519686006033806173011/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6601)
      previous := (0)
      next := (3542)
      square := (122807815867293674619298293000000000000000)
      linear := (-19916089964063277830616516142740000000000000)
      constant := (809734114926697957993543419273444542611489255) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree123.table
  base := (54524063237276588240681930729345336469/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (13363)
      previous := (0)
      next := (6923)
      square := (245615631734587349238596586000000000000000)
      linear := (-40311715209132178581175054191480000000000000)
      constant := (1658586083432247072568224259378648258676565800) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 123 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 123 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (333397828753630671489/100000000000000000000)
  centralHi := (33339782875363067149/10000000000000000000)
  directionLo := (167380712373101446427/50000000000000000000)
  directionHi := (66952284949240578571/20000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree124.table
  base := (1161985790546523819264614630620795846481/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-180683415519586369235374711002660000000000000)
      constant := (7406145543504124862739187355093549693573415445) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree124.table
  base := (5809928952687664510827557670862559333807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-365717736515614000085833132957320000000000000)
      constant := (15170062858344375239395442406762746995991759966) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 124 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 124 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (167380712373101446427/50000000000000000000)
  centralHi := (66952284949240578571/20000000000000000000)
  directionLo := (336119488840769366339/100000000000000000000)
  directionHi := (16805974442038468317/5000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree125.table
  base := (308610011555152170563684748325392595019/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-182122021362603237995200776720660000000000000)
      constant := (7525639135606149885547239031774569664192608220) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree125.table
  base := (3086100115533312305392641202424804588067/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-368630036149038392941090778191320000000000000)
      constant := (15414807080177409919197615891674696197640151692) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 125 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 125 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (336119488840769366339/100000000000000000000)
  centralHi := (16805974442038468317/5000000000000000000)
  directionLo := (168736043911083578693/50000000000000000000)
  directionHi := (337472087822167157387/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree126.table
  base := (1634805026990364762245481676353125497111/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (943)
      previous := (0)
      next := (506)
      square := (17543973695327667802756899000000000000000)
      linear := (-2913660749295557250079791149820000000000000)
      constant := (121366473181654028120891346791680987625271972) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree126.table
  base := (3269610053965978580463452904028132021677/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1260000000000000000000000000000000000000000
      center := (1909)
      previous := (0)
      next := (989)
      square := (35087947390655335605513798000000000000000)
      linear := (-5897497393372425171370609895640000000000000)
      constant := (248595355809286108839652857047935089269462604) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 126 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 126 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (168736043911083578693/50000000000000000000)
  centralHi := (337472087822167157387/100000000000000000000)
  directionLo := (338819287142165097007/100000000000000000000)
  directionHi := (21176205446385318563/6250000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree127.table
  base := (6910988533331871241336382217859745122219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-184999233048636975514852908156660000000000000)
      constant := (7767491567819931797711300711760425328390087211) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree127.table
  base := (1382197706661594808956620337623317005541/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-374454635415887178651606068659320000000000000)
      constant := (15910163865370513040228451202483389451949922290) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 127 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 127 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (338819287142165097007/100000000000000000000)
  centralHi := (21176205446385318563/6250000000000000000)
  directionLo := (340161150956421451619/100000000000000000000)
  directionHi := (17008057547821072581/5000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree128.table
  base := (1821876364542589178640772244023440097327/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-186437838891653844274678973874660000000000000)
      constant := (7889850407538678632359067726465476134985163452) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree128.table
  base := (3643752729075500315234376096635334697503/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-377366935049311571506863713893320000000000000)
      constant := (16160776427944565779960675451557862573657557628) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 128 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 128 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (340161150956421451619/100000000000000000000)
  centralHi := (17008057547821072581/5000000000000000000)
  directionLo := (341497742160134585377/100000000000000000000)
  directionHi := (170748871080067292689/50000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree129.table
  base := (958596354292624782150086977215836221231/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6601)
      previous := (0)
      next := (3542)
      square := (122807815867293674619298293000000000000000)
      linear := (-20875160526074523670500559954740000000000000)
      constant := (890351592156599202238573976580837470188502968) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree129.table
  base := (7668770834325321296747483802048454430601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (13363)
      previous := (0)
      next := (6923)
      square := (245615631734587349238596586000000000000000)
      linear := (-42253248298081773818013484347480000000000000)
      constant := (1823705011480564640610380934247766736807790082) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 129 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 129 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (341497742160134585377/100000000000000000000)
  centralHi := (170748871080067292689/50000000000000000000)
  directionLo := (21426820151402666803/6250000000000000000)
  directionHi := (342829122422442668849/100000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree130.table
  base := (4027392307296306639373646125933933237347/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-189315050577687581794331105310660000000000000)
      constant := (8137433333244534417373892817308263562038060486) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree130.table
  base := (1006848076822489610372229381524493920333/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-383191534316160357217379004361320000000000000)
      constant := (16667869891136982406729538151412131461916826832) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 130 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 130 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21426820151402666803/6250000000000000000)
  centralHi := (342829122422442668849/100000000000000000000)
  directionLo := (2688713689215825537/781250000000000000)
  directionHi := (344155352219625668737/100000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree131.table
  base := (8445546752536243797948456986338549721587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-190753656420704450554157171028660000000000000)
      constant := (8262657418859985649811650012598997703844978803) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree131.table
  base := (8445546752525961891071258543058172889897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-386103833949584750072636649595320000000000000)
      constant := (16924350791012033206865177791838155776400002386) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 131 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 131 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2688713689215825537/781250000000000000)
  centralHi := (344155352219625668737/100000000000000000000)
  directionLo := (86369122716790049151/25000000000000000000)
  directionHi := (69095298173432039321/20000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree132.table
  base := (8841057202623377028912115785268296254951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6601)
      previous := (0)
      next := (3542)
      square := (122807815867293674619298293000000000000000)
      linear := (-21354695807080146590442581860740000000000000)
      constant := (932092954008329385579247970273063318648433391) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree132.table
  base := (353642288104602036946635369679318231307/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (13363)
      previous := (0)
      next := (6923)
      square := (245615631734587349238596586000000000000000)
      linear := (-43224014842556571436432699425480000000000000)
      constant := (1909198644732074547095120978354308967000319350) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 132 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 132 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86369122716790049151/25000000000000000000)
  centralHi := (69095298173432039321/20000000000000000000)
  directionLo := (346792596550675289577/100000000000000000000)
  directionHi := (173396298275337644789/50000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree133.table
  base := (9241315920124867328446607535943871746741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8487)
      previous := (0)
      next := (4554)
      square := (157895763257949010224812091000000000000000)
      linear := (-27661552586676884010544186066380000000000000)
      constant := (1216567262101705842788687181989660175280402147) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree133.table
  base := (1848263184023625075701632120627756909007/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11340000000000000000000000000000000000000000
      center := (17181)
      previous := (0)
      next := (8901)
      square := (315791526515898020449624182000000000000000)
      linear := (-55989776173776219397593134294760000000000000)
      constant := (2491882989358833755788226071327599381674069690) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 133 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 133 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (346792596550675289577/100000000000000000000)
  centralHi := (173396298275337644789/50000000000000000000)
  directionLo := (2175648289724092707/625000000000000000)
  directionHi := (348103726355854833121/100000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree134.table
  base := (4823161430555265872618968963247964215587/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-195069473949755056833635368182660000000000000)
      constant := (8644060164596556041600620393585342339943329606) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree134.table
  base := (4823161430552536423991610444322103618221/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-394840732849857928638409585297320000000000000)
      constant := (17705530159432812074558012061986097717042876596) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 134 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 134 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2175648289724092707/625000000000000000)
  centralHi := (348103726355854833121/100000000000000000000)
  directionLo := (34940993629733010613/10000000000000000000)
  directionHi := (349409936297330106131/100000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree135.table
  base := (502803899121469639208283258106425075309/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6601)
      previous := (0)
      next := (3542)
      square := (122807815867293674619298293000000000000000)
      linear := (-21834231088085769510384603766740000000000000)
      constant := (974789397284171518530503228660798669164225380) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree135.table
  base := (10056077982424973006210840806435289276163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (13363)
      previous := (0)
      next := (6923)
      square := (245615631734587349238596586000000000000000)
      linear := (-44194781387031369054851914503480000000000000)
      constant := (1996648389334340696714504474759675925141575766) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 135 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 135 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34940993629733010613/10000000000000000000)
  centralHi := (349409936297330106131/100000000000000000000)
  directionLo := (350711281346603823241/100000000000000000000)
  directionHi := (175355640673301911621/50000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree136.table
  base := (10470581241690543278456846610595345789963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-197946685635788794353287499618660000000000000)
      constant := (8903104067426654264497614457705772927440363147) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree136.table
  base := (10470581241686965013681588196524402964609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-400665332116706714348924875765320000000000000)
      constant := (18236096958904100224791141259360170710733066242) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 136 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 136 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (350711281346603823241/100000000000000000000)
  centralHi := (175355640673301911621/50000000000000000000)
  directionLo := (44000976932380632591/12500000000000000000)
  directionHi := (352007815459045060729/100000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree137.table
  base := (5444916298622304729122985802971309546783/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-199385291478805663113113565336660000000000000)
      constant := (9034058640038581470277280381027926255182363454) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree137.table
  base := (5444916298620856319709232438099434672773/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-403577631750131107204182520999320000000000000)
      constant := (18504314523787301506638319609980986624864944148) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 137 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 137 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44000976932380632591/12500000000000000000)
  centralHi := (352007815459045060729/100000000000000000000)
  directionLo := (176649795799996286649/50000000000000000000)
  directionHi := (353299591599992573299/100000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree138.table
  base := (1414229001020723678068301937930012791299/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6601)
      previous := (0)
      next := (3542)
      square := (122807815867293674619298293000000000000000)
      linear := (-22313766369091392430326625672740000000000000)
      constant := (1018440921470098975152938768299857085127702872) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree138.table
  base := (2828458002040861100022782407269832600757/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (13363)
      previous := (0)
      next := (6923)
      square := (245615631734587349238596586000000000000000)
      linear := (-45165547931506166673271129581480000000000000)
      constant := (2086054244259311260215266564013767969415470696) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 138 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 138 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (176649795799996286649/50000000000000000000)
  centralHi := (353299591599992573299/100000000000000000000)
  directionLo := (70917332354000446533/20000000000000000000)
  directionHi := (177293330885001116333/50000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree139.table
  base := (5871289717117222644880765815915647708837/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-202262503164839400632765696772660000000000000)
      constant := (9298833026843950440019248968079918411512748106) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree139.table
  base := (11742579434232547050586128263533553698361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-409402231016979892914697811467320000000000000)
      constant := (19046617982224336440748669058415769349257589618) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 139 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 139 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70917332354000446533/20000000000000000000)
  centralHi := (177293330885001116333/50000000000000000000)
  directionLo := (88967269257318159699/25000000000000000000)
  directionHi := (355869077029272638797/100000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree140.table
  base := (12176074835920228235749700479093465600283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8487)
      previous := (0)
      next := (4554)
      square := (157895763257949010224812091000000000000000)
      linear := (-29100158429693752770370251784380000000000000)
      constant := (1347521834388694929535210921904045994995360461) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree140.table
  base := (12176074835918691736584546486502679476811/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11340000000000000000000000000000000000000000
      center := (17181)
      previous := (0)
      next := (8901)
      square := (315791526515898020449624182000000000000000)
      linear := (-58902075807200612252850779528760000000000000)
      constant := (2760100553592159293232363716456894038526703674) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 140 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 140 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88967269257318159699/25000000000000000000)
  centralHi := (355869077029272638797/100000000000000000000)
  directionLo := (178573443760640682589/50000000000000000000)
  directionHi := (357146887521281365179/100000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree141.table
  base := (3153579543591429168343943145468945502833/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6601)
      previous := (0)
      next := (3542)
      square := (122807815867293674619298293000000000000000)
      linear := (-22793301650097015350268647578740000000000000)
      constant := (1063047526078600874474539329135987219866997412) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree141.table
  base := (630715908718223652069191439640174936721/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (13363)
      previous := (0)
      next := (6923)
      square := (245615631734587349238596586000000000000000)
      linear := (-46136314475980964291690344659480000000000000)
      constant := (2177416208531965232597027228985692685883758440) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 141 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 141 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (178573443760640682589/50000000000000000000)
  centralHi := (357146887521281365179/100000000000000000000)
  directionLo := (5600314726494731171/1562500000000000000)
  directionHi := (71684028499132558989/20000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree142.table
  base := (13057309411370548568088496189652323206147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-206578320693890006912243893926660000000000000)
      constant := (9703157708651963293677247576568770070805197443) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree142.table
  base := (1632163676421192753836331359758901701227/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-418139129917253071480470747169320000000000000)
      constant := (19874743986848818193148345787106649293634719408) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 142 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 142 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5600314726494731171/1562500000000000000)
  centralHi := (71684028499132558989/20000000000000000000)
  directionLo := (7193777806607141601/2000000000000000000)
  directionHi := (359688890330357080051/100000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree143.table
  base := (13505048509376029828388070663217747455597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-208016926536906875672069959644660000000000000)
      constant := (9839842762405460320116494587625971239651264493) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree143.table
  base := (6752524254687607612018622102941755034133/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-421051429550677464335728392403320000000000000)
      constant := (20154698205030367522483895047262383302921895508) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 143 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 143 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7193777806607141601/2000000000000000000)
  centralHi := (359688890330357080051/100000000000000000000)
  directionLo := (360953178553058406203/100000000000000000000)
  directionHi := (90238294638264601551/25000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree144.table
  base := (2791507086290040288348670494927834038563/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6601)
      previous := (0)
      next := (3542)
      square := (122807815867293674619298293000000000000000)
      linear := (-23272836931102638270210669484740000000000000)
      constant := (1108609210646812889363095431859235874055031415) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree144.table
  base := (2791507086289908440632946287320466749801/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (13363)
      previous := (0)
      next := (6923)
      square := (245615631734587349238596586000000000000000)
      linear := (-47107081020455761910109559737480000000000000)
      constant := (2270734281226574362106639319224043258366622410) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 144 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 144 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (360953178553058406203/100000000000000000000)
  centralHi := (90238294638264601551/25000000000000000000)
  directionLo := (90553263465497366843/25000000000000000000)
  directionHi := (362213053861989467373/100000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree145.table
  base := (14414770141273348788721684120243279204291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-210894138222940613191722091080660000000000000)
      constant := (10116078108755377398806812256258145575161830979) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree145.table
  base := (1441477014127281530904857462429761912581/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-426876028817526250046243682871320000000000000)
      constant := (20720474964586917563178585482153874500620679780) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 145 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 145 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90553263465497366843/25000000000000000000)
  centralHi := (362213053861989467373/100000000000000000000)
  directionLo := (72693712429205568267/20000000000000000000)
  directionHi := (45433570268253480167/12500000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree146.table
  base := (7438376301561968636848469154098240402863/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-212332744065957481951548156798660000000000000)
      constant := (10255628401065865732923314596979751832317926494) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree146.table
  base := (7438376301561752791445551272463435250987/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-429788328450950642901501328105320000000000000)
      constant := (21006297505390054938265453960498389498044669612) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 146 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 146 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72693712429205568267/20000000000000000000)
  centralHi := (45433570268253480167/12500000000000000000)
  directionLo := (45589968563026101001/12500000000000000000)
  directionHi := (364719748504208808009/100000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree147.table
  base := (3835870695466239770536865885737189102873/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (943)
      previous := (0)
      next := (506)
      square := (17543973695327667802756899000000000000000)
      linear := (-3393196030301180170021813055820000000000000)
      constant := (165017996390687654327008404350985771653923996) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree147.table
  base := (15343482781864609774845441687425406503221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1260000000000000000000000000000000000000000
      center := (1909)
      previous := (0)
      next := (989)
      square := (35087947390655335605513798000000000000000)
      linear := (-6868263937847222789789824973640000000000000)
      constant := (338001208780470854800366267081255601219405846) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 147 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 147 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45589968563026101001/12500000000000000000)
  centralHi := (364719748504208808009/100000000000000000000)
  directionLo := (365966657264628061453/100000000000000000000)
  directionHi := (182983328632314030727/50000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree148.table
  base := (7907480321465338256210021772349771871309/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-215209955751991219471200288234660000000000000)
      constant := (10537594223260555454903595272240672489114450842) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree148.table
  base := (7907480321465196939749158101432924851179/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-435612927717799428612016618573320000000000000)
      constant := (21583810907651361509116477495327229114937317804) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 148 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 148 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (365966657264628061453/100000000000000000000)
  centralHi := (182983328632314030727/50000000000000000000)
  directionLo := (91802333000691682819/25000000000000000000)
  directionHi := (367209332002766731277/100000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree149.table
  base := (16291186152313747936222677769589955655899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-216648561595008088231026353952660000000000000)
      constant := (10680009752872590290906821041206882533998263131) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree149.table
  base := (8145593076156759630707955310519364608689/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-438525227351223821467274263807320000000000000)
      constant := (21875501768565197654257588340920245432527546564) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 149 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 149 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91802333000691682819/25000000000000000000)
  centralHi := (367209332002766731277/100000000000000000000)
  directionLo := (184223907779630073119/50000000000000000000)
  directionHi := (368447815559260146239/100000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree150.table
  base := (262064988696136297168605016881055664297/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6601)
      previous := (0)
      next := (3542)
      square := (122807815867293674619298293000000000000000)
      linear := (-24231907493113884110094713296740000000000000)
      constant := (1202597817924068692692502878273450915069118528) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree150.table
  base := (4193039819138134502256854813949483610481/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (13363)
      previous := (0)
      next := (6923)
      square := (245615631734587349238596586000000000000000)
      linear := (-49048614109405357146947989893480000000000000)
      constant := (2463238748405061701591595367484613778177776968) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 150 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 150 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (184223907779630073119/50000000000000000000)
  centralHi := (368447815559260146239/100000000000000000000)
  directionLo := (369682150057130839461/100000000000000000000)
  directionHi := (184841075028565419731/50000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree151.table
  base := (17257879982719894378535716143082613793803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-219525773281041825750678485388660000000000000)
      constant := (10967706048461949214283185274844514894147604107) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree151.table
  base := (17257879982719744702597856319892263367529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-444349826618072607177789554275320000000000000)
      constant := (22464751808631054363694931077471864786611445202) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 151 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 151 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (369682150057130839461/100000000000000000000)
  centralHi := (184841075028565419731/50000000000000000000)
  directionLo := (370912376918505407739/100000000000000000000)
  directionHi := (18545618845925270387/5000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree152.table
  base := (177483482384094933885876173276411466807/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-220964379124058694510504551106660000000000000)
      constant := (11112986814179964735378751941251647711175698300) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree152.table
  base := (17748348238409372303517630737024094035551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-447262126251497000033047199509320000000000000)
      constant := (22762310987264457823616823717287617258454203838) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 152 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 152 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370912376918505407739/100000000000000000000)
  centralHi := (18545618845925270387/5000000000000000000)
  directionLo := (46517317110104249321/12500000000000000000)
  directionHi := (372138536880833994569/100000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree153.table
  base := (18243564011726218320504119954506240832501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6601)
      previous := (0)
      next := (3542)
      square := (122807815867293674619298293000000000000000)
      linear := (-24711442774119507030036735202740000000000000)
      constant := (1251024739816008038328782044045477252207132941) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree153.table
  base := (1824356401172612036908683680609072199099/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (13363)
      previous := (0)
      next := (6923)
      square := (245615631734587349238596586000000000000000)
      linear := (-50019380653880154765367204971480000000000000)
      constant := (2562425141254731199908431597261492016796053180) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 153 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 153 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46517317110104249321/12500000000000000000)
  centralHi := (372138536880833994569/100000000000000000000)
  directionLo := (373360670012630365153/100000000000000000000)
  directionHi := (186680335006315182577/50000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree154.table
  base := (18743527271274083504952796955221257073087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8487)
      previous := (0)
      next := (4554)
      square := (157895763257949010224812091000000000000000)
      linear := (-31977370115727490290022383220380000000000000)
      constant := (1629487654404237339414637748183250452760440329) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree154.table
  base := (2342940908909250533845536932036129524891/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11340000000000000000000000000000000000000000
      center := (17181)
      previous := (0)
      next := (8901)
      square := (315791526515898020449624182000000000000000)
      linear := (-64726675074049397963366069996760000000000000)
      constant := (3337613951495171709198679024600751767049811152) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 154 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 154 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (373360670012630365153/100000000000000000000)
  centralHi := (186680335006315182577/50000000000000000000)
  directionLo := (374578815728749779511/100000000000000000000)
  directionHi := (46822351966093722439/12500000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree155.table
  base := (3849647597229115727328993563061059406659/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-225280196653109300789982748260660000000000000)
      constant := (11554559581514059919807338690910046723925147855) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree155.table
  base := (19248237986145514545724739615981703038117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-455999025151770178598820135211320000000000000)
      constant := (23666725154539977509145523137828462758716572746) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 155 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 155 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (374578815728749779511/100000000000000000000)
  centralHi := (46822351966093722439/12500000000000000000)
  directionLo := (375793012805221144699/100000000000000000000)
  directionHi := (3757930128052211447/1000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree156.table
  base := (4939424031477781945602166934472558482071/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6601)
      previous := (0)
      next := (3542)
      square := (122807815867293674619298293000000000000000)
      linear := (-25190978055125129949978757108740000000000000)
      constant := (1300406740030721443310544692112489593162373244) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree156.table
  base := (9878848062955537971344844243733468904857/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (13363)
      previous := (0)
      next := (6923)
      square := (245615631734587349238596586000000000000000)
      linear := (-50990147198354952383786420049480000000000000)
      constant := (2663567639252484162788393965738985839148167748) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 156 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 156 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (375793012805221144699/100000000000000000000)
  centralHi := (3757930128052211447/1000000000000000000)
  directionLo := (188501649696824618569/50000000000000000000)
  directionHi := (377003299393649237139/100000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree157.table
  base := (1013595083030441903158057347222452949357/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-228157408339143038309634879696660000000000000)
      constant := (11853716816998041833028075417718858315119958660) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree157.table
  base := (20271901660608796134476424653271318496819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-461823624418618964309335425679320000000000000)
      constant := (24279448456425504330947644422812587726227749222) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 157 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 157 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188501649696824618569/50000000000000000000)
  centralHi := (377003299393649237139/100000000000000000000)
  directionLo := (189104856517601064541/50000000000000000000)
  directionHi := (378209713035202129083/100000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree158.table
  base := (20790854560734528373732574299760983735713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-229596014182159907069460945414660000000000000)
      constant := (12004728051561604354700439197253711344447044897) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree158.table
  base := (2079085456073449446258121906150809025343/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-464735924052043357164593070913320000000000000)
      constant := (24588744263765213920634616730099731220431727340) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 158 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 158 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (189104856517601064541/50000000000000000000)
  centralHi := (378209713035202129083/100000000000000000000)
  directionLo := (94853072668549581921/25000000000000000000)
  directionHi := (75882458134839665537/20000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree159.table
  base := (2131455479723202887996166108303349690707/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6601)
      previous := (0)
      next := (3542)
      square := (122807815867293674619298293000000000000000)
      linear := (-25670513336130752869920779014740000000000000)
      constant := (1350743818205761846304467490298237772136017870) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree159.table
  base := (21314554797232001454323027709413547710537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (13363)
      previous := (0)
      next := (6923)
      square := (245615631734587349238596586000000000000000)
      linear := (-51960913742829750002205635127480000000000000)
      constant := (2766666241673426484542480054024262749080693634) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 159 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 159 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94853072668549581921/25000000000000000000)
  centralHi := (75882458134839665537/20000000000000000000)
  directionLo := (380611068671307539153/100000000000000000000)
  directionHi := (190305534335653769577/50000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree160.table
  base := (21843002341483742391144572291856805906631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-232473225868193644589113076850660000000000000)
      constant := (12309615753755215375897476542885579662643418439) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree160.table
  base := (21843002341483720211524662914098011683007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-470560523318892142875108361381320000000000000)
      constant := (25213204190085211167513025175341710016739709566) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 160 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 160 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380611068671307539153/100000000000000000000)
  centralHi := (190305534335653769577/50000000000000000000)
  directionLo := (3054448662531027221/800000000000000000)
  directionHi := (190903041408189201313/50000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree161.table
  base := (22376197165301459048658100934262682158857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (8487)
      previous := (0)
      next := (4554)
      square := (157895763257949010224812091000000000000000)
      linear := (-33415975958744359049848448938380000000000000)
      constant := (1780498888737114518177624439900986940784071919) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree161.table
  base := (1118809858265072055613898699940712694131/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11340000000000000000000000000000000000000000
      center := (17181)
      previous := (0)
      next := (8901)
      square := (315791526515898020449624182000000000000000)
      linear := (-67638974707473790818623715230760000000000000)
      constant := (3646909758373510618935431985342535363902891080) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 161 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 161 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3054448662531027221/800000000000000000)
  centralHi := (190903041408189201313/50000000000000000000)
  directionLo := (382997368340905997091/100000000000000000000)
  directionHi := (95749342085226499273/25000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree162.table
  base := (22914139240917416099198469077987023371121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6601)
      previous := (0)
      next := (3542)
      square := (122807815867293674619298293000000000000000)
      linear := (-26150048617136375789862800920740000000000000)
      constant := (1402035973995045013378892036370552277306664361) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree162.table
  base := (5728534810229350398705535986140255206969/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (13363)
      previous := (0)
      next := (6923)
      square := (245615631734587349238596586000000000000000)
      linear := (-52931680287304547620624850205480000000000000)
      constant := (2871720947825389706308006587432182820370186632) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 162 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 162 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (382997368340905997091/100000000000000000000)
  centralHi := (95749342085226499273/25000000000000000000)
  directionLo := (384184959930151408549/100000000000000000000)
  directionHi := (7683699198603028171/2000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree163.table
  base := (11728414270487797417131135874169932412229/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-236789043397244250868591274004660000000000000)
      constant := (12774110388033449817143398272625220923488273802) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree163.table
  base := (5864207135243895776409423109820811060309/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-479297422219165321440881297083320000000000000)
      constant := (26164564855309858164907293709100310392786931368) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 163 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 163 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (384184959930151408549/100000000000000000000)
  centralHi := (7683699198603028171/2000000000000000000)
  directionLo := (385368891734925152353/100000000000000000000)
  directionHi := (192684445867462576177/50000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree164.table
  base := (1200213251926162353856861502015227384707/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-238227649240261119628417339722660000000000000)
      constant := (12930852087286960259930109880203648749798041660) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree164.table
  base := (375066641226925587397022665605215807129/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-482209721852589714296138942317320000000000000)
      constant := (26485597283044675842922387353426588996927360128) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 164 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 164 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (385368891734925152353/100000000000000000000)
  centralHi := (192684445867462576177/50000000000000000000)
  directionLo := (386549197383045776027/100000000000000000000)
  directionHi := (96637299345761444007/25000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree165.table
  base := (24556448707002643885219550192241412582301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (6601)
      previous := (0)
      next := (3542)
      square := (122807815867293674619298293000000000000000)
      linear := (-26629583898141998709804822826740000000000000)
      constant := (1454283207067836535844107632514478462948794741) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree165.table
  base := (982257948280105448679504129655384482761/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (13363)
      previous := (0)
      next := (6923)
      square := (245615631734587349238596586000000000000000)
      linear := (-53902446831779345239044065283480000000000000)
      constant := (2978731757046905015475143665217501227844880050) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 165 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 165 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386549197383045776027/100000000000000000000)
  centralHi := (96637299345761444007/25000000000000000000)
  directionLo := (387725909990484519647/100000000000000000000)
  directionHi := (12116434687202641239/3125000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree166.table
  base := (25113379520243039409765334293813344409733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-241104860926294857148069471158660000000000000)
      constant := (13247200716900283814870310179099065163962230277) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree166.table
  base := (5022675904048606641941432524331529733593/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-488034321119438500006654232785320000000000000)
      constant := (27133530446234522674073223936968678415126306170) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 166 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 166 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (387725909990484519647/100000000000000000000)
  centralHi := (12116434687202641239/3125000000000000000)
  directionLo := (19444953108610324151/5000000000000000000)
  directionHi := (388899062172206483021/100000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree167.table
  base := (25675057452452843117686999832574925155583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-242543466769311725907895536876660000000000000)
      constant := (13406807647053858413924309724618029877942508927) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree167.table
  base := (25675057452452838104881647003994435975817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-490946620752862892861911878019320000000000000)
      constant := (27460431181277074802188622911443227832776035346) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 167 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 167 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19444953108610324151/5000000000000000000)
  centralHi := (388899062172206483021/100000000000000000000)
  directionLo := (39006868605271834033/10000000000000000000)
  directionHi := (390068686052718340331/100000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree168.table
  base := (26241482478211993831346809808400448962247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (943)
      previous := (0)
      next := (506)
      square := (17543973695327667802756899000000000000000)
      linear := (-3872731311306803089963834961820000000000000)
      constant := (215355073872545403126109891286249228284621561) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree168.table
  base := (2624148247821198977858891888344954219141/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1260000000000000000000000000000000000000000
      center := (1909)
      previous := (0)
      next := (989)
      square := (35087947390655335605513798000000000000000)
      linear := (-7839030482322020408209040051640000000000000)
      constant := (441099809815047890133663428299474642316117660) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 168 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 168 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell237.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39006868605271834033/10000000000000000000)
  centralHi := (390068686052718340331/100000000000000000000)
  directionLo := (391234813276332252709/100000000000000000000)
  directionHi := (39123481327633225271/10000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree169.table
  base := (3351581821558066160378329829567179867803/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (59409)
      previous := (0)
      next := (31878)
      square := (1105270342805643071573684637000000000000000)
      linear := (-245420678455345463427547668312660000000000000)
      constant := (13728886737550342649691577217900197095162480856) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree169.table
  base := (6703163643116131501640650651957395309649/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (120267)
      previous := (0)
      next := (62307)
      square := (2210540685611286143147369274000000000000000)
      linear := (-496771220019711678572427168487320000000000000)
      constant := (28120100957248455274633516661312591215871975048) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 169 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 169 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell237.Kernel169
