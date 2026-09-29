import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell234.Parameters
import ForestUnimodality.BinomialMassData.Q53_78.Batch000_049
import ForestUnimodality.BinomialMassData.Q53_78.Batch050_099
import ForestUnimodality.BinomialMassData.Q107_156.Batch000_049
import ForestUnimodality.BinomialMassData.Q107_156.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree000.table
  base := (468518114605630813350956027/100000000000000000000000000)
  polynomial :=
    { denominator := 52000000000000000000000000000000000000000
      center := (53)
      previous := (0)
      next := (25)
      square := (2483646039936206612042113304000000000000)
      linear := (-3887454365118759636033018992000000000000)
      constant := (243629419594928022942497134040000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree000.table
  base := (468518114605630813350956027/100000000000000000000000000)
  polynomial :=
    { denominator := 104000000000000000000000000000000000000000
      center := (107)
      previous := (0)
      next := (49)
      square := (4967292079872413224084226608000000000000)
      linear := (-7774908730237519272066037984000000000000)
      constant := (487258839189856045884994268080000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree001.table
  base := (6951134344026735167831536733249100920447/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6084000000000000000000000000000000000000000
      center := (6201)
      previous := (0)
      next := (2925)
      square := (290586586672536173608927256568000000000000)
      linear := (-849731881068751728730559237400000000000000)
      constant := (21588567945136669855708665449925764999999774) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree001.table
  base := (866074919479849821210302401784342743261/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12168000000000000000000000000000000000000000
      center := (12519)
      previous := (0)
      next := (5733)
      square := (581173173345072347217854513136000000000000)
      linear := (-1706914700257312077297244814712000000000000)
      constant := (43050950901825096318581812617262529999999392) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (29549181354690267907/100000000000000000000)
  directionHi := (7387295338672566977/25000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree002.table
  base := (25436914572416215305024002653264809335963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (31005)
      previous := (0)
      next := (14625)
      square := (1452932933362680868044636282840000000000000)
      linear := (-6223158007093042900226276263680000000000000)
      constant := (83152913321167542550539380120231549999999446) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree002.table
  base := (12632085722379594792148678693903114727153/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (62595)
      previous := (0)
      next := (28665)
      square := (2905865866725361736089272565680000000000000)
      linear := (-12520825395384171998813815926480000000000000)
      constant := (165414903231936216627711609217553099999997704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29549181354690267907/100000000000000000000)
  centralHi := (7387295338672566977/25000000000000000000)
  directionLo := (41788853028825162443/100000000000000000000)
  directionHi := (10447213257206290611/25000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree003.table
  base := (3647474379592492014636182396913203210607/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 676000000000000000000000000000000000000000
      center := (689)
      previous := (0)
      next := (325)
      square := (32287398519170685956547472952000000000000)
      linear := (-182170146863162825706661252008000000000000)
      constant := (1470028529558309515402410350962662685185166) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree003.table
  base := (3607672480036644801736665326942079498137/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1352000000000000000000000000000000000000000
      center := (1391)
      previous := (0)
      next := (637)
      square := (64574797038341371913094945904000000000000)
      linear := (-366823939766261858025364617320000000000000)
      constant := (2920181400338910425552426846483845740740612) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41788853028825162443/100000000000000000000)
  centralHi := (10447213257206290611/25000000000000000000)
  directionLo := (25590341714195245039/50000000000000000000)
  directionHi := (51180683428390490079/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree004.table
  base := (3164544038561677605188885567527356874389/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (31005)
      previous := (0)
      next := (14625)
      square := (1452932933362680868044636282840000000000000)
      linear := (-10172155210591611413373236417040000000000000)
      constant := (55420396188189327649271315584392878447565352) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree004.table
  base := (1556749365540388186628577068189247661563/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (62595)
      previous := (0)
      next := (28665)
      square := (2905865866725361736089272565680000000000000)
      linear := (-20493329183579395223468999632320000000000000)
      constant := (110122113255635784175306059579147062183594336) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25590341714195245039/50000000000000000000)
  centralHi := (51180683428390490079/100000000000000000000)
  directionLo := (29549181354690267907/50000000000000000000)
  directionHi := (11819672541876107163/20000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree005.table
  base := (8321892058443683082960375830778071348657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (31005)
      previous := (0)
      next := (14625)
      square := (1452932933362680868044636282840000000000000)
      linear := (-12146653812340895669946716493720000000000000)
      constant := (49812092265009229227544300713576893042614594) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree005.table
  base := (1625026929244759217869389224442550242851/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12168000000000000000000000000000000000000000
      center := (12519)
      previous := (0)
      next := (5733)
      square := (581173173345072347217854513136000000000000)
      linear := (-4895916215535401367159318297048000000000000)
      constant := (19841745848040042165700726017563475677505484) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29549181354690267907/50000000000000000000)
  centralHi := (11819672541876107163/20000000000000000000)
  directionLo := (66073978188556763199/100000000000000000000)
  directionHi := (41296236367847977/62500000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree006.table
  base := (991150603499500302409939433022627773023/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 676000000000000000000000000000000000000000
      center := (689)
      previous := (0)
      next := (325)
      square := (32287398519170685956547472952000000000000)
      linear := (-313803386979781776144893257120000000000000)
      constant := (1077702579655725699326332325009648187281774) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree006.table
  base := (596675801111723460419691830216567540039/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6955)
      previous := (0)
      next := (3185)
      square := (322873985191706859565474729520000000000000)
      linear := (-3162870330197179827569353704240000000000000)
      constant := (10774930723756434860240849966511197256530912) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66073978188556763199/100000000000000000000)
  centralHi := (41296236367847977/62500000000000000)
  directionLo := (36190208317976873241/50000000000000000000)
  directionHi := (72380416635953746483/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree007.table
  base := (1162735255512247537698930416894172962347/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (31005)
      previous := (0)
      next := (14625)
      square := (1452932933362680868044636282840000000000000)
      linear := (-16095651015839464183093676647080000000000000)
      constant := (50761261967677483311246063893534148302919148) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree007.table
  base := (2160887181087548496211497451288966798047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (62595)
      previous := (0)
      next := (28665)
      square := (2905865866725361736089272565680000000000000)
      linear := (-32452084865872230060451775191080000000000000)
      constant := (101971531354361077573781504183957073999317948) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36190208317976873241/50000000000000000000)
  centralHi := (72380416635953746483/100000000000000000000)
  directionLo := (39089892655028565693/50000000000000000000)
  directionHi := (78179785310057131387/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree008.table
  base := (65844168218091425135898727401553508149/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (31005)
      previous := (0)
      next := (14625)
      square := (1452932933362680868044636282840000000000000)
      linear := (-18070149617588748439667156723760000000000000)
      constant := (56095984265683419015800439315342103087157032) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree008.table
  base := (3675405951663082357262153260459403403/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (62595)
      previous := (0)
      next := (28665)
      square := (2905865866725361736089272565680000000000000)
      linear := (-36438336759969841672779367044000000000000000)
      constant := (113166132954070986737518498230292320329723264) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39089892655028565693/50000000000000000000)
  centralHi := (78179785310057131387/100000000000000000000)
  directionLo := (41788853028825162443/50000000000000000000)
  directionHi := (83577706057650324887/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree009.table
  base := (-1358961044224311052437483783860184511229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (3445)
      previous := (0)
      next := (1625)
      square := (161436992595853429782737364760000000000000)
      linear := (-2227183135482003632915626311160000000000000)
      constant := (7123343463304893604122011918685257635204598) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree009.table
  base := (-1486245754822536335963072052623917395011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6955)
      previous := (0)
      next := (3185)
      square := (322873985191706859565474729520000000000000)
      linear := (-4491620961563050365011884321880000000000000)
      constant := (14418699786260590502085816656461231840972564) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41788853028825162443/50000000000000000000)
  centralHi := (83577706057650324887/100000000000000000000)
  directionLo := (88647544064070803721/100000000000000000000)
  directionHi := (44323772032035401861/50000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree010.table
  base := (-21120654216769064930555057560128151107/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6084000000000000000000000000000000000000000
      center := (6201)
      previous := (0)
      next := (2925)
      square := (290586586672536173608927256568000000000000)
      linear := (-4403829364217463390562823375424000000000000)
      constant := (14900765325124134932728107722992254108312650) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree010.table
  base := (-2750028546634547354850099828102376853087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (62595)
      previous := (0)
      next := (28665)
      square := (2905865866725361736089272565680000000000000)
      linear := (-44410840548165064897434550749840000000000000)
      constant := (151173645252495909497594254756125139225818692) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88647544064070803721/100000000000000000000)
  centralHi := (44323772032035401861/50000000000000000000)
  directionLo := (93442716074201041839/100000000000000000000)
  directionHi := (1168033950927513023/1250000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree011.table
  base := (-3655723753841493087432430875981288791257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (31005)
      previous := (0)
      next := (14625)
      square := (1452932933362680868044636282840000000000000)
      linear := (-23993645422836601209387596953800000000000000)
      constant := (87046794943438005417390867816174919496996206) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree011.table
  base := (-3749884289908499994443661391058137894989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (62595)
      previous := (0)
      next := (28665)
      square := (2905865866725361736089272565680000000000000)
      linear := (-48397092442262676509762142602760000000000000)
      constant := (176918884544954900646544353735077289046886924) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93442716074201041839/100000000000000000000)
  centralHi := (1168033950927513023/1250000000000000000)
  directionLo := (98003547415673299907/100000000000000000000)
  directionHi := (24500886853918324977/25000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree012.table
  base := (-4464205876400614209584893147517236949327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (3445)
      previous := (0)
      next := (1625)
      square := (161436992595853429782737364760000000000000)
      linear := (-2885349336065098385106786336720000000000000)
      constant := (11284621113721541732298261983339173911127474) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree012.table
  base := (-454429367916592315404667823985355212993/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1352000000000000000000000000000000000000000
      center := (1391)
      previous := (0)
      next := (637)
      square := (64574797038341371913094945904000000000000)
      linear := (-1164074318585784180490882987904000000000000)
      constant := (4592182653516740136494748276643799752033464) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98003547415673299907/100000000000000000000)
  centralHi := (24500886853918324977/25000000000000000000)
  directionLo := (102361366856780980157/100000000000000000000)
  directionHi := (51180683428390490079/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree013.table
  base := (-5110515161722328589262258256799505839761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2340000000000000000000000000000000000000000
      center := (2385)
      previous := (0)
      next := (1125)
      square := (111764071797129297541895098680000000000000)
      linear := (-2149434048179628440194965931320000000000000)
      constant := (9070104720017687531968626955898915633495926) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree013.table
  base := (-161820362475313147814183046037883276689/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 4680000000000000000000000000000000000000000
      center := (4815)
      previous := (0)
      next := (2205)
      square := (223528143594258595083790197360000000000000)
      linear := (-4336122786958299979570563562200000000000000)
      constant := (18468300074096033344545139454551660048305536) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102361366856780980157/100000000000000000000)
  centralHi := (51180683428390490079/50000000000000000000)
  directionLo := (106541088522320226451/100000000000000000000)
  directionHi := (26635272130580056613/25000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree014.table
  base := (-2814708026539921469943881497311904671699/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (31005)
      previous := (0)
      next := (14625)
      square := (1452932933362680868044636282840000000000000)
      linear := (-29917141228084453979108037183840000000000000)
      constant := (135990355517209097569880759228474371977383284) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree014.table
  base := (-2843219896440217004897902104171904432083/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (62595)
      previous := (0)
      next := (28665)
      square := (2905865866725361736089272565680000000000000)
      linear := (-60355848124555511346744918161520000000000000)
      constant := (277026925486503905064894373582576266870414056) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106541088522320226451/100000000000000000000)
  centralHi := (26635272130580056613/25000000000000000000)
  directionLo := (110562912688899661017/100000000000000000000)
  directionHi := (55281456344449830509/50000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree015.table
  base := (-6047819859299507885351460105621715495063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (3445)
      previous := (0)
      next := (1625)
      square := (161436992595853429782737364760000000000000)
      linear := (-3543515536648193137297946362280000000000000)
      constant := (17301856476997955106186293756249860162668706) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree015.table
  base := (-6095637970201647842367963616413845816793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6955)
      previous := (0)
      next := (3185)
      square := (322873985191706859565474729520000000000000)
      linear := (-7149122224294791439896945557160000000000000)
      constant := (35255818358025639453087740671979240227847932) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110562912688899661017/100000000000000000000)
  centralHi := (55281456344449830509/50000000000000000000)
  directionLo := (28610871820194531437/25000000000000000000)
  directionHi := (114443487280778125749/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree016.table
  base := (-3193296876054886322503718019001248774509/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (31005)
      previous := (0)
      next := (14625)
      square := (1452932933362680868044636282840000000000000)
      linear := (-33866138431583022492254997337200000000000000)
      constant := (177026941751149490547704673184556402455887244) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree016.table
  base := (-6426559682556744574641530084828551759579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (62595)
      previous := (0)
      next := (28665)
      square := (2905865866725361736089272565680000000000000)
      linear := (-68328351912750734571400101867360000000000000)
      constant := (360788198923814310519408343651903091094721364) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28610871820194531437/25000000000000000000)
  centralHi := (114443487280778125749/100000000000000000000)
  directionLo := (29549181354690267907/25000000000000000000)
  directionHi := (118196725418761071629/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree017.table
  base := (-6661944518912030266437042885317223489089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (31005)
      previous := (0)
      next := (14625)
      square := (1452932933362680868044636282840000000000000)
      linear := (-35840637033332306748828477413880000000000000)
      constant := (199871754844437743695222374294815006146191262) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree017.table
  base := (-1673813234320336760458953222324450102147/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (62595)
      previous := (0)
      next := (28665)
      square := (2905865866725361736089272565680000000000000)
      linear := (-72314603806848346183727693720280000000000000)
      constant := (407386790514624642060276128761427182314150608) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29549181354690267907/25000000000000000000)
  centralHi := (118196725418761071629/100000000000000000000)
  directionLo := (121834395875919927343/100000000000000000000)
  directionHi := (7614649742244995459/6250000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree018.table
  base := (-6886479064064708996211197346139080771637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (3445)
      previous := (0)
      next := (1625)
      square := (161436992595853429782737364760000000000000)
      linear := (-4201681737231287889489106387840000000000000)
      constant := (24912533041087557408017890948884990699186694) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree018.table
  base := (-3457085423007113102931128178645094838911/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6955)
      previous := (0)
      next := (3185)
      square := (322873985191706859565474729520000000000000)
      linear := (-8477872855660661977339476174800000000000000)
      constant := (50780263918161274129791532676451831777792328) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121834395875919927343/100000000000000000000)
  centralHi := (7614649742244995459/6250000000000000000)
  directionLo := (125366559086475487329/100000000000000000000)
  directionHi := (12536655908647548733/10000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree019.table
  base := (-88375234032159210208434635152757678091/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6084000000000000000000000000000000000000000
      center := (6201)
      previous := (0)
      next := (2925)
      square := (290586586672536173608927256568000000000000)
      linear := (-7957926847366175052395087513448000000000000)
      constant := (50004038565223063711245501429258978291954848) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree019.table
  base := (-7092991640339714962599358514838056518821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (62595)
      previous := (0)
      next := (28665)
      square := (2905865866725361736089272565680000000000000)
      linear := (-80287107595043569408382877426120000000000000)
      constant := (509636070809335704504426557641440264139493036) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (125366559086475487329/100000000000000000000)
  centralHi := (12536655908647548733/10000000000000000000)
  directionLo := (128801895389451177721/100000000000000000000)
  directionHi := (64400947694725588861/50000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree020.table
  base := (-7220225715475683656605999437816846713107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (31005)
      previous := (0)
      next := (14625)
      square := (1452932933362680868044636282840000000000000)
      linear := (-41764132838580159518548917643920000000000000)
      constant := (277270632737017277624078445732561152298728506) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree020.table
  base := (-7239247936508263682199466069421905948219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (62595)
      previous := (0)
      next := (28665)
      square := (2905865866725361736089272565680000000000000)
      linear := (-84273359489141181020710469279040000000000000)
      constant := (565182048715009614017177542053237124211035604) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (128801895389451177721/100000000000000000000)
  centralHi := (64400947694725588861/50000000000000000000)
  directionLo := (66073978188556763199/50000000000000000000)
  directionHi := (132147956377113526399/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree021.table
  base := (-7343085977521515067328265774541893448033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (3445)
      previous := (0)
      next := (1625)
      square := (161436992595853429782737364760000000000000)
      linear := (-4859847937814382641680266413400000000000000)
      constant := (33993989765443398074287567175194840014564846) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree021.table
  base := (-7358810534584836391619795520128373427407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6955)
      previous := (0)
      next := (3185)
      square := (322873985191706859565474729520000000000000)
      linear := (-9806623487026532514782006792440000000000000)
      constant := (69291621225875328285152115793668219563072868) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66073978188556763199/50000000000000000000)
  centralHi := (132147956377113526399/100000000000000000000)
  directionLo := (13541136028184590431/10000000000000000000)
  directionHi := (135411360281845904311/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree022.table
  base := (-1860820490171246766729518121546757387291/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (31005)
      previous := (0)
      next := (14625)
      square := (1452932933362680868044636282840000000000000)
      linear := (-45713130042078728031695877797280000000000000)
      constant := (336031774263128025882767762575619056111443112) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree022.table
  base := (-7456261065998690031387968644232718152823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (62595)
      previous := (0)
      next := (28665)
      square := (2905865866725361736089272565680000000000000)
      linear := (-92245863277336404245365652984880000000000000)
      constant := (684935823117325126925831007017828142758224868) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13541136028184590431/10000000000000000000)
  centralHi := (135411360281845904311/100000000000000000000)
  directionLo := (34649486478979967599/25000000000000000000)
  directionHi := (138597945915919870397/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree023.table
  base := (-7524480992887164490715354595652388128969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (31005)
      previous := (0)
      next := (14625)
      square := (1452932933362680868044636282840000000000000)
      linear := (-47687628643828012288269357873960000000000000)
      constant := (367517075847893728037513337389495435311676302) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree023.table
  base := (-7535179541960731262656954643324740793689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (62595)
      previous := (0)
      next := (28665)
      square := (2905865866725361736089272565680000000000000)
      linear := (-96232115171434015857693244837800000000000000)
      constant := (749093964180143974969108772055207277011196124) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34649486478979967599/25000000000000000000)
  centralHi := (138597945915919870397/100000000000000000000)
  directionLo := (70856447714454018589/50000000000000000000)
  directionHi := (141712895428908037179/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree024.table
  base := (-7589558701282358291675812957030174959133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (3445)
      previous := (0)
      next := (1625)
      square := (161436992595853429782737364760000000000000)
      linear := (-5518014138397477393871426438960000000000000)
      constant := (44488118331720475023770398557803800863813046) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree024.table
  base := (-7598366622478119340826807963384928131427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6955)
      previous := (0)
      next := (3185)
      square := (322873985191706859565474729520000000000000)
      linear := (-11135374118392403052224537410080000000000000)
      constant := (90675775000650104642927600667311788583155348) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70856447714454018589/50000000000000000000)
  centralHi := (141712895428908037179/100000000000000000000)
  directionLo := (36190208317976873241/25000000000000000000)
  directionHi := (28952166654381498593/20000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree025.table
  base := (-7640772409076553043222226991471511935171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (31005)
      previous := (0)
      next := (14625)
      square := (1452932933362680868044636282840000000000000)
      linear := (-51636625847326580801416318027320000000000000)
      constant := (434652874898707062339676416468693660693209818) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree025.table
  base := (-478000982147321448393374256898049864327/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (62595)
      previous := (0)
      next := (28665)
      square := (2905865866725361736089272565680000000000000)
      linear := (-104204618959629239082348428543640000000000000)
      constant := (885886510907436565658865849235391234006952512) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36190208317976873241/25000000000000000000)
  centralHi := (28952166654381498593/20000000000000000000)
  directionLo := (29549181354690267907/20000000000000000000)
  directionHi := (9234119173340708721/6250000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree026.table
  base := (-7679895921489780261193071262679387841981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2340000000000000000000000000000000000000000
      center := (2385)
      previous := (0)
      next := (1125)
      square := (111764071797129297541895098680000000000000)
      linear := (-4123932649928912696768446008000000000000000)
      constant := (36176239205544827195658552777853023244976446) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree026.table
  base := (-240182701193654074282427243614348988653/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 4680000000000000000000000000000000000000000
      center := (4815)
      previous := (0)
      next := (2205)
      square := (223528143594258595083790197360000000000000)
      linear := (-8322374681055911591898155415120000000000000)
      constant := (73730546901013519552554753125531509545932672) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29549181354690267907/20000000000000000000)
  centralHi := (9234119173340708721/6250000000000000000)
  directionLo := (4708495385570554893/3125000000000000000)
  directionHi := (150671852338257756577/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree027.table
  base := (-7708324458579216506945153583577629577649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (3445)
      previous := (0)
      next := (1625)
      square := (161436992595853429782737364760000000000000)
      linear := (-6176180338980572146062586464520000000000000)
      constant := (56367058338466379747326720731500761202754638) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree027.table
  base := (-7713208296232206318077362941386957670467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6955)
      previous := (0)
      next := (3185)
      square := (322873985191706859565474729520000000000000)
      linear := (-12464124749758273589667068027720000000000000)
      constant := (114878395672385826468252396481457416614764308) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4708495385570554893/3125000000000000000)
  centralHi := (150671852338257756577/100000000000000000000)
  directionLo := (30708410057034294047/20000000000000000000)
  directionHi := (38385512571292867559/25000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree028.table
  base := (-7727156466414057350577444710572537439209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (31005)
      previous := (0)
      next := (14625)
      square := (1452932933362680868044636282840000000000000)
      linear := (-57560121652574433571136758257360000000000000)
      constant := (545686779548108561962573248841958341109926222) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree028.table
  base := (-7731161313450789956196766703473145821727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (62595)
      previous := (0)
      next := (28665)
      square := (2905865866725361736089272565680000000000000)
      linear := (-116163374641922073919331204102400000000000000)
      constant := (1112105415730300727206805120170389380820612932) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30708410057034294047/20000000000000000000)
  centralHi := (38385512571292867559/25000000000000000000)
  directionLo := (156359570620114262773/100000000000000000000)
  directionHi := (78179785310057131387/50000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree029.table
  base := (-7737257490372852213884273667661494771651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (31005)
      previous := (0)
      next := (14625)
      square := (1452932933362680868044636282840000000000000)
      linear := (-59534620254323717827710238334040000000000000)
      constant := (585438240188774638912361123996443732904637658) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree029.table
  base := (-7740538855137144933834813230474207103723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (62595)
      previous := (0)
      next := (28665)
      square := (2905865866725361736089272565680000000000000)
      linear := (-120149626536019685531658795955320000000000000)
      constant := (1193091603555269944360213995119909923980949268) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156359570620114262773/100000000000000000000)
  centralHi := (78179785310057131387/50000000000000000000)
  directionLo := (159127211510913099131/100000000000000000000)
  directionHi := (39781802877728274783/25000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree030.table
  base := (-193482752744947107018289677487689860047/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 676000000000000000000000000000000000000000
      center := (689)
      previous := (0)
      next := (325)
      square := (32287398519170685956547472952000000000000)
      linear := (-1366869307912733379650749298016000000000000)
      constant := (13923462901374142736221864496753286618432912) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree030.table
  base := (-7741996625816415211182301654757223929121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6955)
      previous := (0)
      next := (3185)
      square := (322873985191706859565474729520000000000000)
      linear := (-13792875381124144127109598645360000000000000)
      constant := (141873348357783234868966374584484116623914204) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (159127211510913099131/100000000000000000000)
  centralHi := (39781802877728274783/25000000000000000000)
  directionLo := (161847531837749225819/100000000000000000000)
  directionHi := (8092376591887461291/5000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree031.table
  base := (-386692651245127983393236331418948380717/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6084000000000000000000000000000000000000000
      center := (6201)
      previous := (0)
      next := (2925)
      square := (290586586672536173608927256568000000000000)
      linear := (-12696723491564457268171439697480000000000000)
      constant := (133807582388248946641660450939876236103435544) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree031.table
  base := (-483503183620017644548990571804690796769/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (62595)
      previous := (0)
      next := (28665)
      square := (2905865866725361736089272565680000000000000)
      linear := (-128122130324214908756313979661160000000000000)
      constant := (1363407869479803885192925797713919179079318464) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161847531837749225819/100000000000000000000)
  centralHi := (8092376591887461291/5000000000000000000)
  directionLo := (82261439448722911753/50000000000000000000)
  directionHi := (164522878897445823507/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree032.table
  base := (-7721311688949040684581618541023415073253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (31005)
      previous := (0)
      next := (14625)
      square := (1452932933362680868044636282840000000000000)
      linear := (-65458116059571570597430678564080000000000000)
      constant := (712883190098176071402431889268606771347164374) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree032.table
  base := (-3861554317923238839361040401477191330173/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (62595)
      previous := (0)
      next := (28665)
      square := (2905865866725361736089272565680000000000000)
      linear := (-132108382218312520368641571514080000000000000)
      constant := (1452732331093218460395436583432265535894454936) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82261439448722911753/50000000000000000000)
  centralHi := (164522878897445823507/100000000000000000000)
  directionLo := (167155412115300649773/100000000000000000000)
  directionHi := (83577706057650324887/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree033.table
  base := (-3851011170759991485166971314961257893679/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (3445)
      previous := (0)
      next := (1625)
      square := (161436992595853429782737364760000000000000)
      linear := (-7492512740146761650444906515640000000000000)
      constant := (84232293576868888806351199570316189663872996) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree033.table
  base := (-7703490521440851931153675534735479083847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6955)
      previous := (0)
      next := (3185)
      square := (322873985191706859565474729520000000000000)
      linear := (-15121626012490014664552129263000000000000000)
      constant := (171647952033540298249225388208873816139319428) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (167155412115300649773/100000000000000000000)
  centralHi := (83577706057650324887/50000000000000000000)
  directionLo := (169747123445931696363/100000000000000000000)
  directionHi := (42436780861482924091/25000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree034.table
  base := (-1919062721109746054844052930378455339269/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (31005)
      previous := (0)
      next := (14625)
      square := (1452932933362680868044636282840000000000000)
      linear := (-69407113263070139110577638717440000000000000)
      constant := (804659459348829132586566747274074955431774808) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree034.table
  base := (-3838724855850029684164167283199296623921/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (62595)
      previous := (0)
      next := (28665)
      square := (2905865866725361736089272565680000000000000)
      linear := (-140080886006507743593296755219920000000000000)
      constant := (1639704041141928911985150346820970958680129272) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (169747123445931696363/100000000000000000000)
  centralHi := (42436780861482924091/25000000000000000000)
  directionLo := (172299855011258640349/100000000000000000000)
  directionHi := (3445997100225172807/2000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree035.table
  base := (-7644207721845450745589422463223930215089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (31005)
      previous := (0)
      next := (14625)
      square := (1452932933362680868044636282840000000000000)
      linear := (-71381611864819423367151118794120000000000000)
      constant := (852589001519811397383823750890822804285699262) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree035.table
  base := (-3822593019703428657514931587327516617913/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (62595)
      previous := (0)
      next := (28665)
      square := (2905865866725361736089272565680000000000000)
      linear := (-144067137900605355205624347072840000000000000)
      constant := (1737348533830766848057817470952073777793234616) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (172299855011258640349/100000000000000000000)
  centralHi := (3445997100225172807/2000000000000000000)
  directionLo := (1748153144196272187/1000000000000000000)
  directionHi := (174815314419627218701/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree036.table
  base := (-7606059438239022332298416689282782613341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (3445)
      previous := (0)
      next := (1625)
      square := (161436992595853429782737364760000000000000)
      linear := (-8150678940729856402636066541200000000000000)
      constant := (100208751328302098825339737569262419476690742) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree036.table
  base := (-7606857360229470928227942375524517761659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6955)
      previous := (0)
      next := (3185)
      square := (322873985191706859565474729520000000000000)
      linear := (-16450376643855885201994659880640000000000000)
      constant := (204196009552721223400669591885745425993118516) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1748153144196272187/1000000000000000000)
  centralHi := (174815314419627218701/100000000000000000000)
  directionLo := (88647544064070803721/50000000000000000000)
  directionHi := (177295088128141607443/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree037.table
  base := (-7561937996292455549061674063813101385701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (31005)
      previous := (0)
      next := (14625)
      square := (1452932933362680868044636282840000000000000)
      linear := (-75330609068317991880298078947480000000000000)
      constant := (952528339223101083234671513833430545584697558) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree037.table
  base := (-7562588438608257240729281098796644832803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (62595)
      previous := (0)
      next := (28665)
      square := (2905865866725361736089272565680000000000000)
      linear := (-152039641688800578430279530778680000000000000)
      constant := (1940949938506246267442180897751036212837226548) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88647544064070803721/50000000000000000000)
  centralHi := (177295088128141607443/100000000000000000000)
  directionLo := (35948130629059349811/20000000000000000000)
  directionHi := (351055963174407713/195312500000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree038.table
  base := (-7511947987132417415017210778055210434621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (31005)
      previous := (0)
      next := (14625)
      square := (1452932933362680868044636282840000000000000)
      linear := (-77305107670067276136871559024160000000000000)
      constant := (1004537415158750657731447532767276049857882918) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree038.table
  base := (-7512477936597930306011517286969986189537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (62595)
      previous := (0)
      next := (28665)
      square := (2905865866725361736089272565680000000000000)
      linear := (-156025893582898190042607122631600000000000000)
      constant := (2046905491166091738264923234047894604022856892) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35948130629059349811/20000000000000000000)
  centralHi := (351055963174407713/195312500000000000)
  directionLo := (45538346829780619179/25000000000000000000)
  directionHi := (182153387319122476717/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree039.table
  base := (-1864043087457689393697960478938100253503/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 260000000000000000000000000000000000000000
      center := (265)
      previous := (0)
      next := (125)
      square := (12418230199681033060210566520000000000000)
      linear := (-677603472408688550371325120520000000000000)
      constant := (9041929380008641421362657465300437573635688) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree039.table
  base := (-3728301957427808982113504462610333399029/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 520000000000000000000000000000000000000000
      center := (535)
      previous := (0)
      next := (245)
      square := (24836460399362066120421133040000000000000)
      linear := (-1367625175017058133802860807560000000000000)
      constant := (18424190333615294506792875127183525326500984) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45538346829780619179/25000000000000000000)
  centralHi := (182153387319122476717/100000000000000000000)
  directionLo := (92267289207175995913/50000000000000000000)
  directionHi := (184534578414351991827/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree040.table
  base := (-3697338443265730826934749930701562420359/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (31005)
      previous := (0)
      next := (14625)
      square := (1452932933362680868044636282840000000000000)
      linear := (-81254104873565844650018519177520000000000000)
      constant := (1112633105959760244665899563538411694234535844) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree040.table
  base := (-1479005633119799896963833420031442117781/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12168000000000000000000000000000000000000000
      center := (12519)
      previous := (0)
      next := (5733)
      square := (581173173345072347217854513136000000000000)
      linear := (-32799679474218682653452461267488000000000000)
      constant := (453424779232617412771283330439568706155420396) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92267289207175995913/50000000000000000000)
  centralHi := (184534578414351991827/100000000000000000000)
  directionLo := (186885432148402083679/100000000000000000000)
  directionHi := (1168033950927513023/625000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree041.table
  base := (-7327513829190065437467421062878296329487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (31005)
      previous := (0)
      next := (14625)
      square := (1452932933362680868044636282840000000000000)
      linear := (-83228603475315128906591999254200000000000000)
      constant := (1168719361765389512972222619787634222565700546) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree041.table
  base := (-1465559925559769862322057682407327418407/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12168000000000000000000000000000000000000000
      center := (12519)
      previous := (0)
      next := (5733)
      square := (581173173345072347217854513136000000000000)
      linear := (-33596929853038204975917979638072000000000000)
      constant := (476277214962337273246731833696808819986411812) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186885432148402083679/100000000000000000000)
  centralHi := (1168033950927513023/625000000000000000)
  directionLo := (473017698321290181/250000000000000000)
  directionHi := (189207079328516072401/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree042.table
  base := (-7254724658876405032640234494861081775713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (3445)
      previous := (0)
      next := (1625)
      square := (161436992595853429782737364760000000000000)
      linear := (-9467011341896045907018386592320000000000000)
      constant := (136240486521387156642304434538536954359809006) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree042.table
  base := (-7254957080652231896690290356981539049921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6955)
      previous := (0)
      next := (3185)
      square := (322873985191706859565474729520000000000000)
      linear := (-19107877906587626276879721115920000000000000)
      constant := (277601841005128047144442097854740479602253404) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (473017698321290181/250000000000000000)
  centralHi := (189207079328516072401/100000000000000000000)
  directionLo := (95750291104987964171/50000000000000000000)
  directionHi := (191500582209975928343/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree043.table
  base := (-287053693422232925887760198031066217383/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6084000000000000000000000000000000000000000
      center := (6201)
      previous := (0)
      next := (2925)
      square := (290586586672536173608927256568000000000000)
      linear := (-17435520135762739483947791881512000000000000)
      constant := (256993611295366072514861077522881482833604570) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree043.table
  base := (-7176531269067349957762210528264605761243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (62595)
      previous := (0)
      next := (28665)
      square := (2905865866725361736089272565680000000000000)
      linear := (-175957153053386248104245081896200000000000000)
      constant := (2618215191814463732720870508106233138548597588) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95750291104987964171/50000000000000000000)
  centralHi := (191500582209975928343/100000000000000000000)
  directionLo := (193766940176832342907/100000000000000000000)
  directionHi := (48441735044208085727/25000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree044.table
  base := (-3546196531282031443234734566304070548939/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (31005)
      previous := (0)
      next := (14625)
      square := (1452932933362680868044636282840000000000000)
      linear := (-89152099280562981676312439484240000000000000)
      constant := (1345130315407880040826472529042926034780255124) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree044.table
  base := (-7092546581824667924897872019696087486957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (62595)
      previous := (0)
      next := (28665)
      square := (2905865866725361736089272565680000000000000)
      linear := (-179943404947483859716572673749120000000000000)
      constant := (2740781794735279945903777079022009003729353612) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193766940176832342907/100000000000000000000)
  centralHi := (48441735044208085727/25000000000000000000)
  directionLo := (39201418966269319963/20000000000000000000)
  directionHi := (24500886853918324977/12500000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree045.table
  base := (-87536221044636792066007758817263380199/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 676000000000000000000000000000000000000000
      center := (689)
      previous := (0)
      next := (325)
      square := (32287398519170685956547472952000000000000)
      linear := (-2025035508495828131841909323576000000000000)
      constant := (31258913157315330106443937031186239639883808) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree045.table
  base := (-875377797151213176929766216783998482393/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6955)
      previous := (0)
      next := (3185)
      square := (322873985191706859565474729520000000000000)
      linear := (-20436628537953496814322251733560000000000000)
      constant := (318457362225865773610755203578907136207218656) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39201418966269319963/20000000000000000000)
  centralHi := (24500886853918324977/12500000000000000000)
  directionLo := (198221934565670289597/100000000000000000000)
  directionHi := (99110967282835144799/50000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree046.table
  base := (-863484098636515986712604456380895928091/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (31005)
      previous := (0)
      next := (14625)
      square := (1452932933362680868044636282840000000000000)
      linear := (-93101096484061550189459399637600000000000000)
      constant := (1469530336022411156675576089958674516693977424) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree046.table
  base := (-1381594806130409485944567129225577464713/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12168000000000000000000000000000000000000000
      center := (12519)
      previous := (0)
      next := (5733)
      square := (581173173345072347217854513136000000000000)
      linear := (-37583181747135816588245571490992000000000000)
      constant := (598843698832577237471572421652011586704686108) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198221934565670289597/100000000000000000000)
  centralHi := (99110967282835144799/50000000000000000000)
  directionLo := (25051537334840241583/12500000000000000000)
  directionHi := (40082459735744386533/20000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree047.table
  base := (-272293263732678719109860708505758638841/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6084000000000000000000000000000000000000000
      center := (6201)
      previous := (0)
      next := (2925)
      square := (290586586672536173608927256568000000000000)
      linear := (-19015119017162166889206575942856000000000000)
      constant := (306753601407995987840393479904497411103228390) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree047.table
  base := (-6807413763020370217195799744492154084411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (62595)
      previous := (0)
      next := (28665)
      square := (2905865866725361736089272565680000000000000)
      linear := (-191902160629776694553555449307880000000000000)
      constant := (3125088422773797594185356767197224734550443476) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25051537334840241583/12500000000000000000)
  centralHi := (40082459735744386533/20000000000000000000)
  directionLo := (202578981092367092331/100000000000000000000)
  directionHi := (50644745273091773083/25000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree048.table
  base := (-6701284629208440616922758674707406274721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (3445)
      previous := (0)
      next := (1625)
      square := (161436992595853429782737364760000000000000)
      linear := (-10783343743062235411400706643440000000000000)
      constant := (177707119232291425148517400654028896679144302) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree048.table
  base := (-6701351295757383611343171401117819736711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6955)
      previous := (0)
      next := (3185)
      square := (322873985191706859565474729520000000000000)
      linear := (-21765379169319367351764782351200000000000000)
      constant := (362080665191140970705816786249324353857983364) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (202578981092367092331/100000000000000000000)
  centralHi := (50644745273091773083/25000000000000000000)
  directionLo := (102361366856780980157/50000000000000000000)
  directionHi := (40944546742712392063/20000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree049.table
  base := (-1647435074936572610170832305573877095521/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (31005)
      previous := (0)
      next := (14625)
      square := (1452932933362680868044636282840000000000000)
      linear := (-99024592289309402959179839867640000000000000)
      constant := (1666318508612475434916845338626047063501700472) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree049.table
  base := (-6589794369246839205055786871940518442949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (62595)
      previous := (0)
      next := (28665)
      square := (2905865866725361736089272565680000000000000)
      linear := (-199874664417971917778210633013720000000000000)
      constant := (3395131138909804869167697187619028885793098284) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102361366856780980157/50000000000000000000)
  centralHi := (40944546742712392063/20000000000000000000)
  directionLo := (4136885389656637507/2000000000000000000)
  directionHi := (206844269482831875351/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree050.table
  base := (-6472705315239390937850633831162018217451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (31005)
      previous := (0)
      next := (14625)
      square := (1452932933362680868044636282840000000000000)
      linear := (-100999090891058687215753319944320000000000000)
      constant := (1734631293192778171789535843326605140582514058) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree050.table
  base := (-6472749153106985888635015544016995338037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (62595)
      previous := (0)
      next := (28665)
      square := (2905865866725361736089272565680000000000000)
      linear := (-203860916312069529390538224866640000000000000)
      constant := (3534303841806448566382801569971700600363382892) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4136885389656637507/2000000000000000000)
  centralHi := (206844269482831875351/100000000000000000000)
  directionLo := (26118033143015726527/12500000000000000000)
  directionHi := (208944265144125812217/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree051.table
  base := (-317509252018451324625106194183532509381/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 676000000000000000000000000000000000000000
      center := (689)
      previous := (0)
      next := (325)
      square := (32287398519170685956547472952000000000000)
      linear := (-2288301988729066032718373333800000000000000)
      constant := (40095609122492679330185878064061864047316888) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree051.table
  base := (-396888785690530560122048025623702292673/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6955)
      previous := (0)
      next := (3185)
      square := (322873985191706859565474729520000000000000)
      linear := (-23094129800685237889207312968840000000000000)
      constant := (408471562828260460034804835202529036002448832) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26118033143015726527/12500000000000000000)
  centralHi := (208944265144125812217/100000000000000000000)
  directionLo := (105511681883276701703/50000000000000000000)
  directionHi := (211023363766553403407/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree052.table
  base := (-3111091884841009553962775595835181198097/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2340000000000000000000000000000000000000000
      center := (2385)
      previous := (0)
      next := (1125)
      square := (111764071797129297541895098680000000000000)
      linear := (-8072929853427481209915406161360000000000000)
      constant := (144256295962049322814563846637149135199290604) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree052.table
  base := (-1555553139541591237610232563768927321343/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4680000000000000000000000000000000000000000
      center := (4815)
      previous := (0)
      next := (2205)
      square := (223528143594258595083790197360000000000000)
      linear := (-16294878469251134816553339120960000000000000)
      constant := (293919368147105654647561187779904568054445904) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105511681883276701703/50000000000000000000)
  centralHi := (211023363766553403407/100000000000000000000)
  directionLo := (213082177044640452903/100000000000000000000)
  directionHi := (26635272130580056613/12500000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree053.table
  base := (-3044352473174940082267750283207049649919/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (31005)
      previous := (0)
      next := (14625)
      square := (1452932933362680868044636282840000000000000)
      linear := (-106922586696306539985473760174360000000000000)
      constant := (1947719593702062314363211156531238309929892804) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree053.table
  base := (-1522182066194619884925572010382670232109/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (62595)
      previous := (0)
      next := (28665)
      square := (2905865866725361736089272565680000000000000)
      linear := (-215819671994362364227521000425400000000000000)
      constant := (3968426984014002781866749987041522337231395376) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (213082177044640452903/100000000000000000000)
  centralHi := (26635272130580056613/12500000000000000000)
  directionLo := (53780321850106030297/25000000000000000000)
  directionHi := (215121287400424121189/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree054.table
  base := (-5949751335926630945107354620578891673043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (3445)
      previous := (0)
      next := (1625)
      square := (161436992595853429782737364760000000000000)
      linear := (-12099676144228424915783026694560000000000000)
      constant := (224607293409513176715311694413324334614511466) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree054.table
  base := (-2974885108980593487308939716985798425051/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6955)
      previous := (0)
      next := (3185)
      square := (322873985191706859565474729520000000000000)
      linear := (-24422880432051108426649843586480000000000000)
      constant := (457629960487166601714750102375495200529331048) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53780321850106030297/25000000000000000000)
  centralHi := (215121287400424121189/100000000000000000000)
  directionLo := (217141249907861239447/100000000000000000000)
  directionHi := (27142656238482654931/12500000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree055.table
  base := (-5805325164400189650983973398600441336407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (31005)
      previous := (0)
      next := (14625)
      square := (1452932933362680868044636282840000000000000)
      linear := (-110871583899805108498620720327720000000000000)
      constant := (2096569981685854777644627305593807457454649906) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree055.table
  base := (-2902670224798070274798112887003390614103/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (62595)
      previous := (0)
      next := (28665)
      square := (2905865866725361736089272565680000000000000)
      linear := (-223792175782557587452176184131240000000000000)
      constant := (4271679754661895432473116800310217743007594696) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217141249907861239447/100000000000000000000)
  centralHi := (27142656238482654931/12500000000000000000)
  directionLo := (219142594057569337027/100000000000000000000)
  directionHi := (54785648514392334257/25000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree056.table
  base := (-2827714113951973160298622128885291634293/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (31005)
      previous := (0)
      next := (14625)
      square := (1452932933362680868044636282840000000000000)
      linear := (-112846082501554392755194200404400000000000000)
      constant := (2173032611238933103486767522812021885696961388) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree056.table
  base := (-5655440597898112867754502932308194300891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (62595)
      previous := (0)
      next := (28665)
      square := (2905865866725361736089272565680000000000000)
      linear := (-227778427676655199064503775984160000000000000)
      constant := (4427457304879292156470482725836636945873379156) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (219142594057569337027/100000000000000000000)
  centralHi := (54785648514392334257/25000000000000000000)
  directionLo := (44225165075559864407/20000000000000000000)
  directionHi := (55281456344449830509/25000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree057.table
  base := (-2750030989964539521830203970781789515483/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (3445)
      previous := (0)
      next := (1625)
      square := (161436992595853429782737364760000000000000)
      linear := (-12757842344811519667974186720120000000000000)
      constant := (250094836102592600468368691448101510287533492) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree057.table
  base := (-2750035993968673631329110299667889103131/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6955)
      previous := (0)
      next := (3185)
      square := (322873985191706859565474729520000000000000)
      linear := (-25751631063416978964092374204120000000000000)
      constant := (509555809663884691887048459666884013932566888) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44225165075559864407/20000000000000000000)
  centralHi := (55281456344449830509/25000000000000000000)
  directionLo := (22309142692570096531/10000000000000000000)
  directionHi := (223091426925700965311/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree058.table
  base := (-5339227600669834259731131112608481401271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (31005)
      previous := (0)
      next := (14625)
      square := (1452932933362680868044636282840000000000000)
      linear := (-116795079705052961268341160557760000000000000)
      constant := (2330032719148904782161144984268764999577333618) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree058.table
  base := (-5339235695519403339222430811513655916831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (62595)
      previous := (0)
      next := (28665)
      square := (2905865866725361736089272565680000000000000)
      linear := (-235750931464850422289158959690000000000000000)
      constant := (4747314694403704619375673857216570917402000196) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22309142692570096531/10000000000000000000)
  centralHi := (223091426925700965311/100000000000000000000)
  directionLo := (225039860661345390539/100000000000000000000)
  directionHi := (11251993033067269527/5000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree059.table
  base := (-5172926052176823135901064218071363551951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (31005)
      previous := (0)
      next := (14625)
      square := (1452932933362680868044636282840000000000000)
      linear := (-118769578306802245524914640634440000000000000)
      constant := (2410570190989089278153955005859296912074965058) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree059.table
  base := (-1034586519575214615558351633970480984117/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12168000000000000000000000000000000000000000
      center := (12519)
      previous := (0)
      next := (5733)
      square := (581173173345072347217854513136000000000000)
      linear := (-47947436671789606780297310308584000000000000)
      constant := (982278904365688222247755838081586593692632172) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (225039860661345390539/100000000000000000000)
  centralHi := (11251993033067269527/5000000000000000000)
  directionLo := (226971568715577510349/100000000000000000000)
  directionHi := (4539431374311550207/2000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree060.table
  base := (-1250289530558715020703506625177750533029/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (3445)
      previous := (0)
      next := (1625)
      square := (161436992595853429782737364760000000000000)
      linear := (-13416008545394614420165346745680000000000000)
      constant := (276940659783049498528507754407559681279344792) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree060.table
  base := (-500116341390189055451750487220733278229/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1352000000000000000000000000000000000000000
      center := (1391)
      previous := (0)
      next := (637)
      square := (64574797038341371913094945904000000000000)
      linear := (-5416076338956569900306980964352000000000000)
      constant := (112849816997231496827854391422317568607834392) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (226971568715577510349/100000000000000000000)
  centralHi := (4539431374311550207/2000000000000000000)
  directionLo := (228886974561556251497/100000000000000000000)
  directionHi := (114443487280778125749/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree061.table
  base := (-4823924459280536082290497522981259679487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (31005)
      previous := (0)
      next := (14625)
      square := (1452932933362680868044636282840000000000000)
      linear := (-122718575510300814038061600787800000000000000)
      constant := (2575719958351429298202291436866001008055000546) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree061.table
  base := (-2411964368050996416066951472506665106397/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (62595)
      previous := (0)
      next := (28665)
      square := (2905865866725361736089272565680000000000000)
      linear := (-247709687147143257126141735248760000000000000)
      constant := (5247856419939832103530004060356813898985361304) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228886974561556251497/100000000000000000000)
  centralHi := (114443487280778125749/50000000000000000000)
  directionLo := (46157296819755323953/20000000000000000000)
  directionHi := (115393242049388309883/50000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree062.table
  base := (-4641225600197836771744360583455352200419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (31005)
      previous := (0)
      next := (14625)
      square := (1452932933362680868044636282840000000000000)
      linear := (-124693074112050098294635080864480000000000000)
      constant := (2660332250267839628182106914458928818606325402) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree062.table
  base := (-4641229055967048165765945381462676554107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (62595)
      previous := (0)
      next := (28665)
      square := (2905865866725361736089272565680000000000000)
      linear := (-251695939041240868738469327101680000000000000)
      constant := (5420238484031456124404268072094921075844813012) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46157296819755323953/20000000000000000000)
  centralHi := (115393242049388309883/50000000000000000000)
  directionLo := (116335243328717081147/50000000000000000000)
  directionHi := (46534097331486832459/20000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree063.table
  base := (-445306199245180534415587284843464597759/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 676000000000000000000000000000000000000000
      center := (689)
      previous := (0)
      next := (325)
      square := (32287398519170685956547472952000000000000)
      linear := (-2814834949195541834471301354248000000000000)
      constant := (61028951387455284784510450669931817931914916) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree063.table
  base := (-4453064784134756595014925332009645499639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6955)
      previous := (0)
      next := (3185)
      square := (322873985191706859565474729520000000000000)
      linear := (-28409132326148720038977435439400000000000000)
      constant := (621709772739107739203922820187916479642244036) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116335243328717081147/50000000000000000000)
  centralHi := (46534097331486832459/20000000000000000000)
  directionLo := (2931741949127142427/1250000000000000000)
  directionHi := (234539355930171394161/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree064.table
  base := (-4259434011720048786479178209652601618799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (31005)
      previous := (0)
      next := (14625)
      square := (1452932933362680868044636282840000000000000)
      linear := (-128642071315548666807782041017840000000000000)
      constant := (2833631643711562579110567028211356785875613442) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree064.table
  base := (-851887253283080608144089854136032172947/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12168000000000000000000000000000000000000000
      center := (12519)
      previous := (0)
      next := (5733)
      square := (581173173345072347217854513136000000000000)
      linear := (-51933688565887218392624902161504000000000000)
      constant := (1154660965939492583072945564671564380259790452) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2931741949127142427/1250000000000000000)
  centralHi := (234539355930171394161/100000000000000000000)
  directionLo := (236393450837522143257/100000000000000000000)
  directionHi := (118196725418761071629/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree065.table
  base := (-2030170987971800303136396360612932652171/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2340000000000000000000000000000000000000000
      center := (2385)
      previous := (0)
      next := (1125)
      square := (111764071797129297541895098680000000000000)
      linear := (-10047428455176765466488886238040000000000000)
      constant := (224793749471452868898069550216583147518783972) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree065.table
  base := (-4060343796535594467825213778920651655543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4680000000000000000000000000000000000000000
      center := (4815)
      previous := (0)
      next := (2205)
      square := (223528143594258595083790197360000000000000)
      linear := (-20281130363348746428880930973880000000000000)
      constant := (457999162106223325785986463930240135025205876) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (236393450837522143257/100000000000000000000)
  centralHi := (118196725418761071629/50000000000000000000)
  directionLo := (47646623266546129279/20000000000000000000)
  directionHi := (59558279083182661599/25000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree066.table
  base := (-3855786156529465868042372855890050607789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (3445)
      previous := (0)
      next := (1625)
      square := (161436992595853429782737364760000000000000)
      linear := (-14732340946560803924547666796800000000000000)
      constant := (334707123317982428398861716329949162894567318) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree066.table
  base := (-3855787626277389231327130498834450769201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6955)
      previous := (0)
      next := (3185)
      square := (322873985191706859565474729520000000000000)
      linear := (-29737882957514590576419966057040000000000000)
      constant := (681937865130049841040309634496287911280020124) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47646623266546129279/20000000000000000000)
  centralHi := (59558279083182661599/25000000000000000000)
  directionLo := (60014671037764147507/25000000000000000000)
  directionHi := (240058684151056590029/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree067.table
  base := (-72915335745738666452151726020901824229/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6084000000000000000000000000000000000000000
      center := (6201)
      previous := (0)
      next := (2925)
      square := (290586586672536173608927256568000000000000)
      linear := (-26913113424159303915500496249576000000000000)
      constant := (620753548639835680495025496313634166506953820) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree067.table
  base := (-1822883986774923349057874076877166875763/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (62595)
      previous := (0)
      next := (28665)
      square := (2905865866725361736089272565680000000000000)
      linear := (-271627198511728926800107286366280000000000000)
      constant := (6323659864740340200611459847045473633455715816) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60014671037764147507/25000000000000000000)
  centralHi := (240058684151056590029/100000000000000000000)
  directionLo := (48374094701635140129/20000000000000000000)
  directionHi := (120935236754087850323/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree068.table
  base := (-3430284071560401238310997038407661947521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (31005)
      previous := (0)
      next := (14625)
      square := (1452932933362680868044636282840000000000000)
      linear := (-136540065722545803834075961324560000000000000)
      constant := (3196529642522323276798722176979083892355641118) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree068.table
  base := (-686057005763786891880349480447343099383/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12168000000000000000000000000000000000000000
      center := (12519)
      previous := (0)
      next := (5733)
      square := (581173173345072347217854513136000000000000)
      linear := (-55122690081165307682486975643840000000000000)
      constant := (1302529268386356636427783531940622364583353828) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48374094701635140129/20000000000000000000)
  centralHi := (120935236754087850323/50000000000000000000)
  directionLo := (121834395875919927343/50000000000000000000)
  directionHi := (243668791751839854687/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree069.table
  base := (-3209338187926652791341780272389846826979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (3445)
      previous := (0)
      next := (1625)
      square := (161436992595853429782737364760000000000000)
      linear := (-15390507147143898676738826822360000000000000)
      constant := (365627756365338433793174673581162231772481098) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree069.table
  base := (-1604669480116837691383306578305487094297/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6955)
      previous := (0)
      next := (3185)
      square := (322873985191706859565474729520000000000000)
      linear := (-31066633588880461113862496674680000000000000)
      constant := (744933357413528762090977154914765981448510456) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121834395875919927343/50000000000000000000)
  centralHi := (243668791751839854687/100000000000000000000)
  directionLo := (61363483742641006333/25000000000000000000)
  directionHi := (245453934970564025333/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree070.table
  base := (-186433080921823648606928567495846130827/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (31005)
      previous := (0)
      next := (14625)
      square := (1452932933362680868044636282840000000000000)
      linear := (-140489062926044372347222921477920000000000000)
      constant := (3386128237014604546710011915406242177120388256) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree070.table
  base := (-2982929917716608118723143325774709016657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (62595)
      previous := (0)
      next := (28665)
      square := (2905865866725361736089272565680000000000000)
      linear := (-283585954194021761637090061925040000000000000)
      constant := (6898921488198138505501370188157086670342658812) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61363483742641006333/25000000000000000000)
  centralHi := (245453934970564025333/100000000000000000000)
  directionLo := (123613094281376849967/50000000000000000000)
  directionHi := (49445237712550739987/20000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree071.table
  base := (-2200846027057813070458418214980531579/8000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6084000000000000000000000000000000000000000
      center := (6201)
      previous := (0)
      next := (2925)
      square := (290586586672536173608927256568000000000000)
      linear := (-28492712305558731320759280310920000000000000)
      constant := (696592986254132195876153969836089305734170500) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree071.table
  base := (-2751058036231282201124229033443840044789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (62595)
      previous := (0)
      next := (28665)
      square := (2905865866725361736089272565680000000000000)
      linear := (-287572206088119373249417653777960000000000000)
      constant := (7096210155539803886822684051879002677167503724) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (123613094281376849967/50000000000000000000)
  centralHi := (49445237712550739987/20000000000000000000)
  directionLo := (248985827769370486571/100000000000000000000)
  directionHi := (62246456942342621643/25000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree072.table
  base := (-2513723033289989024017912695491544657403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (3445)
      previous := (0)
      next := (1625)
      square := (161436992595853429782737364760000000000000)
      linear := (-16048673347726993428929986847920000000000000)
      constant := (397906654407377881561923354755323857905797786) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree072.table
  base := (-2513723438395612030681932773540383542567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6955)
      previous := (0)
      next := (3185)
      square := (322873985191706859565474729520000000000000)
      linear := (-32395384220246331651305027292320000000000000)
      constant := (810696246444527512396533755242846700725224708) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (248985827769370486571/100000000000000000000)
  centralHi := (62246456942342621643/25000000000000000000)
  directionLo := (250733118172950974659/100000000000000000000)
  directionHi := (12536655908647548733/5000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree073.table
  base := (-2270925909987373057510566408947439108161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (31005)
      previous := (0)
      next := (14625)
      square := (1452932933362680868044636282840000000000000)
      linear := (-146412558731292225116943361707960000000000000)
      constant := (3680713111846412259755615295951451890232974238) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree073.table
  base := (-2270926236575096819572590639367171897873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (62595)
      previous := (0)
      next := (28665)
      square := (2905865866725361736089272565680000000000000)
      linear := (-295544709876314596474072837483800000000000000)
      constant := (7499089674897337982532848595285285126173340668) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (250733118172950974659/100000000000000000000)
  centralHi := (12536655908647548733/5000000000000000000)
  directionLo := (126234158082770304189/50000000000000000000)
  directionHi := (252468316165540608379/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree074.table
  base := (-1011333135660478359909688199078373613193/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (31005)
      previous := (0)
      next := (14625)
      square := (1452932933362680868044636282840000000000000)
      linear := (-148387057333041509373516841784640000000000000)
      constant := (3781624597483964267024066708689327174937333788) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree074.table
  base := (-1011333267281147048804639447547418694629/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (62595)
      previous := (0)
      next := (28665)
      square := (2905865866725361736089272565680000000000000)
      linear := (-299530961770412208086400429336720000000000000)
      constant := (7704680525598101079703435690186783009323754328) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (126234158082770304189/50000000000000000000)
  centralHi := (252468316165540608379/100000000000000000000)
  directionLo := (50838333877575393357/20000000000000000000)
  directionHi := (127095834693938483393/50000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree075.table
  base := (-884472108391006072338121246436675416149/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (3445)
      previous := (0)
      next := (1625)
      square := (161436992595853429782737364760000000000000)
      linear := (-16706839548310088181121146873480000000000000)
      constant := (431543816252933834003539110192158807418683276) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree075.table
  base := (-1768944428927021728311249831943354421277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6955)
      previous := (0)
      next := (3185)
      square := (322873985191706859565474729520000000000000)
      linear := (-33724134851612202188747557909960000000000000)
      constant := (879226529946167347910990438994481292411216748) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50838333877575393357/20000000000000000000)
  centralHi := (127095834693938483393/50000000000000000000)
  directionLo := (255903417141952450393/100000000000000000000)
  directionHi := (127951708570976225197/50000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree076.table
  base := (-301951967833336277622853441126209740107/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6084000000000000000000000000000000000000000
      center := (6201)
      previous := (0)
      next := (2925)
      square := (290586586672536173608927256568000000000000)
      linear := (-30467210907308015577332760387600000000000000)
      constant := (797504471588289422528903689445726069970594506) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree076.table
  base := (-377440002526094039946394032120675833151/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (62595)
      previous := (0)
      next := (28665)
      square := (2905865866725361736089272565680000000000000)
      linear := (-307503465558607431311055613042560000000000000)
      constant := (8124164406099346010228999947399511232924437264) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (255903417141952450393/100000000000000000000)
  centralHi := (127951708570976225197/50000000000000000000)
  directionLo := (257603790778902355443/100000000000000000000)
  directionHi := (64400947694725588861/25000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree077.table
  base := (-622556612781069710672684470559414523683/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (31005)
      previous := (0)
      next := (14625)
      square := (1452932933362680868044636282840000000000000)
      linear := (-154310553138289362143237282014680000000000000)
      constant := (4092508632214172900599639419399866522037912628) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree077.table
  base := (-1245113363273856519765586543506425181761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (62595)
      previous := (0)
      next := (28665)
      square := (2905865866725361736089272565680000000000000)
      linear := (-311489717452705042923383204895480000000000000)
      constant := (8338057434831388644100564107365821909194166076) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (257603790778902355443/100000000000000000000)
  centralHi := (64400947694725588861/25000000000000000000)
  directionLo := (2025726672374987517/781250000000000000)
  directionHi := (259293014063998402177/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree078.table
  base := (-487502229072927938858728246383752755753/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 260000000000000000000000000000000000000000
      center := (265)
      previous := (0)
      next := (125)
      square := (12418230199681033060210566520000000000000)
      linear := (-1335769672991783302562485146080000000000000)
      constant := (35887633921748700916859577518748044856700844) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree078.table
  base := (-975004569071932938920603164798151759739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 520000000000000000000000000000000000000000
      center := (535)
      previous := (0)
      next := (245)
      square := (24836460399362066120421133040000000000000)
      linear := (-2696375806382928671245391425200000000000000)
      constant := (73117246625820869645629181839890496108493572) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2025726672374987517/781250000000000000)
  centralHi := (259293014063998402177/100000000000000000000)
  directionLo := (260971303520377979821/100000000000000000000)
  directionHi := (130485651760188989911/50000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree079.table
  base := (-699433614835447029311950353217562536021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (31005)
      previous := (0)
      next := (14625)
      square := (1452932933362680868044636282840000000000000)
      linear := (-158259550341787930656384242168040000000000000)
      constant := (4306555967595697043963640216970982174765424118) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree079.table
  base := (-139886740834340940458061929524985357127/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12168000000000000000000000000000000000000000
      center := (12519)
      previous := (0)
      next := (5733)
      square := (581173173345072347217854513136000000000000)
      linear := (-63892444248180053229607677720264000000000000)
      constant := (1754829133360365237498593803148992989087239332) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (260971303520377979821/100000000000000000000)
  centralHi := (130485651760188989911/50000000000000000000)
  directionLo := (262638868753003928141/100000000000000000000)
  directionHi := (131319434376501964071/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree080.table
  base := (-104600192454746529723850253807173716549/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (31005)
      previous := (0)
      next := (14625)
      square := (1452932933362680868044636282840000000000000)
      linear := (-160234048943537214912957722244720000000000000)
      constant := (4415617028241789891868352514633274310217031768) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree080.table
  base := (-418400841756392876864669142252484654299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (62595)
      previous := (0)
      next := (28665)
      square := (2905865866725361736089272565680000000000000)
      linear := (-323448473134997877760365980454240000000000000)
      constant := (8996340869128495243992061392992935883363244884) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (262638868753003928141/100000000000000000000)
  centralHi := (131319434376501964071/50000000000000000000)
  directionLo := (66073978188556763199/25000000000000000000)
  directionHi := (264295912754227052797/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree081.table
  base := (-131905993989573314397634215149786397657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (3445)
      previous := (0)
      next := (1625)
      square := (161436992595853429782737364760000000000000)
      linear := (-18023171949476277685503466924600000000000000)
      constant := (502892927840802193363984992532269372197591934) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree081.table
  base := (-26381210381586579327520622653505099781/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1352000000000000000000000000000000000000000
      center := (1391)
      previous := (0)
      next := (637)
      square := (64574797038341371913094945904000000000000)
      linear := (-7276327222868788652726523829048000000000000)
      constant := (204917854706103787174566053084901230552548044) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66073978188556763199/25000000000000000000)
  centralHi := (264295912754227052797/100000000000000000000)
  directionLo := (66485658048053102791/25000000000000000000)
  directionHi := (53188526438442482233/20000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree082.table
  base := (160050644696862226442179559237532210059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (31005)
      previous := (0)
      next := (14625)
      square := (1452932933362680868044636282840000000000000)
      linear := (-164183046147035783426104682398080000000000000)
      constant := (4637813934365264652688334914818600572982999478) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree082.table
  base := (80025299036209150761844941983245103339/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (62595)
      previous := (0)
      next := (28665)
      square := (2905865866725361736089272565680000000000000)
      linear := (-331420976923193100985021164160080000000000000)
      constant := (9449033444330890876879301967216992126417428952) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66485658048053102791/25000000000000000000)
  centralHi := (53188526438442482233/20000000000000000000)
  directionLo := (267579217683389507419/100000000000000000000)
  directionHi := (13378960884169475371/5000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree083.table
  base := (457469080925399566641262154541397992267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (31005)
      previous := (0)
      next := (14625)
      square := (1452932933362680868044636282840000000000000)
      linear := (-166157544748785067682678162474760000000000000)
      constant := (4750949779437236639615460849575184932692476214) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree083.table
  base := (91493808679600286517954233312071610567/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12168000000000000000000000000000000000000000
      center := (12519)
      previous := (0)
      next := (5733)
      square := (581173173345072347217854513136000000000000)
      linear := (-67081445763458142519469751202600000000000000)
      constant := (1935906163280598914194686204647109643678689628) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (267579217683389507419/100000000000000000000)
  centralHi := (13378960884169475371/5000000000000000000)
  directionLo := (269205854049994839717/100000000000000000000)
  directionHi := (134602927024997419859/50000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree084.table
  base := (380174625887767075351585036278711818101/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (3445)
      previous := (0)
      next := (1625)
      square := (161436992595853429782737364760000000000000)
      linear := (-18681338150059372437694626950160000000000000)
      constant := (540604876176859058466602506215404409189036276) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree084.table
  base := (760349221574485841914462990384290191759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6955)
      previous := (0)
      next := (3185)
      square := (322873985191706859565474729520000000000000)
      linear := (-37710386745709813801075149762880000000000000)
      constant := (1101421730845640666381665801275659780169629084) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269205854049994839717/100000000000000000000)
  centralHi := (134602927024997419859/50000000000000000000)
  directionLo := (13541136028184590431/5000000000000000000)
  directionHi := (270822720563691808621/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree085.table
  base := (106869109651452540644894197818846595243/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6084000000000000000000000000000000000000000
      center := (6201)
      previous := (0)
      next := (2925)
      square := (290586586672536173608927256568000000000000)
      linear := (-34021308390456727239165024525624000000000000)
      constant := (996259250528800063123930326705519862685458412) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree085.table
  base := (213738214442575668764835277427774596133/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12168000000000000000000000000000000000000000
      center := (12519)
      previous := (0)
      next := (5733)
      square := (581173173345072347217854513136000000000000)
      linear := (-68675946521097187164400787943768000000000000)
      constant := (2029765545517359704344469483334005580642873172) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13541136028184590431/5000000000000000000)
  centralHi := (270822720563691808621/100000000000000000000)
  directionLo := (136214995588088495337/50000000000000000000)
  directionHi := (10897199647047079627/4000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree086.table
  base := (345623639105748241917780799810501814893/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (31005)
      previous := (0)
      next := (14625)
      square := (1452932933362680868044636282840000000000000)
      linear := (-172081040554032920452398602704800000000000000)
      constant := (5098506880415418652802145005229254186083618024) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree086.table
  base := (1382494536871008561509806687746212966973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (62595)
      previous := (0)
      next := (28665)
      square := (2905865866725361736089272565680000000000000)
      linear := (-347365984499583547434331531571760000000000000)
      constant := (10387627265975529979262990045996147959691063732) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136214995588088495337/50000000000000000000)
  centralHi := (10897199647047079627/4000000000000000000)
  directionLo := (274027834737612463541/100000000000000000000)
  directionHi := (137013917368806231771/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree087.table
  base := (850879787323308277974944504226392461079/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (3445)
      previous := (0)
      next := (1625)
      square := (161436992595853429782737364760000000000000)
      linear := (-19339504350642467189885786975720000000000000)
      constant := (579675085414781743939994396024807041303689404) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree087.table
  base := (1701759558918066402349021393094339206503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6955)
      previous := (0)
      next := (3185)
      square := (322873985191706859565474729520000000000000)
      linear := (-39039137377075684338517680380520000000000000)
      constant := (1181021576936935391272600647614966773303596028) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (274027834737612463541/100000000000000000000)
  centralHi := (137013917368806231771/50000000000000000000)
  directionLo := (68904103800915145017/25000000000000000000)
  directionHi := (275616415203660580069/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree088.table
  base := (126655381004314135744808874351828118233/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (31005)
      previous := (0)
      next := (14625)
      square := (1452932933362680868044636282840000000000000)
      linear := (-176030037757531488965545562858160000000000000)
      constant := (5337002917429187446054986949769572178170636576) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree088.table
  base := (1013243041708930962799193971311277161227/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (62595)
      previous := (0)
      next := (28665)
      square := (2905865866725361736089272565680000000000000)
      linear := (-355338488287778770658986715277600000000000000)
      constant := (10873528506623232368694111720587235620497810136) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68904103800915145017/25000000000000000000)
  centralHi := (275616415203660580069/100000000000000000000)
  directionLo := (34649486478979967599/12500000000000000000)
  directionHi := (277195891831839740793/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree089.table
  base := (1178337033600975361298704531626576856827/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (31005)
      previous := (0)
      next := (14625)
      square := (1452932933362680868044636282840000000000000)
      linear := (-178004536359280773222119042934840000000000000)
      constant := (5458288326341162583922427597960286093596935468) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree089.table
  base := (117833702851367412264554863061147187007/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12168000000000000000000000000000000000000000
      center := (12519)
      previous := (0)
      next := (5733)
      square := (581173173345072347217854513136000000000000)
      linear := (-71864948036375276454262861426104000000000000)
      constant := (2224126041644686484746177131148159077943002352) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34649486478979967599/12500000000000000000)
  centralHi := (277195891831839740793/100000000000000000000)
  directionLo := (139383209683933391713/50000000000000000000)
  directionHi := (278766419367866783427/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree090.table
  base := (2692323436089475562221123278165611892417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (3445)
      previous := (0)
      next := (1625)
      square := (161436992595853429782737364760000000000000)
      linear := (-19997670551225561942076947001280000000000000)
      constant := (620103555034545690745537628992219976819636946) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree090.table
  base := (673080856976910101202987986642346019541/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6955)
      previous := (0)
      next := (3185)
      square := (322873985191706859565474729520000000000000)
      linear := (-40367888008441554875960210998160000000000000)
      constant := (1263388810768625656720853419222180903636838864) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139383209683933391713/50000000000000000000)
  centralHi := (278766419367866783427/100000000000000000000)
  directionLo := (280328148222603125519/100000000000000000000)
  directionHi := (3504101852782539069/1250000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree091.table
  base := (3033434152223883238540134092106754152563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2340000000000000000000000000000000000000000
      center := (2385)
      previous := (0)
      next := (1125)
      square := (111764071797129297541895098680000000000000)
      linear := (-13996425658675333979635846391400000000000000)
      constant := (438841071091137605225190913317622980471699742) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree091.table
  base := (606686829129062798487820461955035589319/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 936000000000000000000000000000000000000000
      center := (963)
      previous := (0)
      next := (441)
      square := (44705628718851719016758039472000000000000)
      linear := (-5650726830308793930707222935944000000000000)
      constant := (178817473421524808536055097520869956655801292) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (280328148222603125519/100000000000000000000)
  centralHi := (3504101852782539069/1250000000000000000)
  directionLo := (70470306160044335929/25000000000000000000)
  directionHi := (281881224640177343717/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree092.table
  base := (3380006166471049315418311174906344243313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (31005)
      previous := (0)
      next := (14625)
      square := (1452932933362680868044636282840000000000000)
      linear := (-183928032164528625991839483164880000000000000)
      constant := (5830294112813329531040631126093265099188158146) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree092.table
  base := (3380006161182205720887085742239685952097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (62595)
      previous := (0)
      next := (28665)
      square := (2905865866725361736089272565680000000000000)
      linear := (-371283495864169217108297082689280000000000000)
      constant := (11878539634369407491358742598800826249332558148) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70470306160044335929/25000000000000000000)
  centralHi := (281881224640177343717/100000000000000000000)
  directionLo := (70856447714454018589/25000000000000000000)
  directionHi := (283425790857816074357/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree093.table
  base := (74640788620075243820305787306844891261/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 676000000000000000000000000000000000000000
      center := (689)
      previous := (0)
      next := (325)
      square := (32287398519170685956547472952000000000000)
      linear := (-4131167350361731338853621405368000000000000)
      constant := (132378056912245396185699733977823135732462180) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree093.table
  base := (3732039426752287358360575938869390873701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6955)
      previous := (0)
      next := (3185)
      square := (322873985191706859565474729520000000000000)
      linear := (-41696638639807425413402741615800000000000000)
      constant := (1348523431393100800474546865288030708230621876) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70856447714454018589/25000000000000000000)
  centralHi := (283425790857816074357/100000000000000000000)
  directionLo := (142480992628938819457/50000000000000000000)
  directionHi := (56992397051575527783/20000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree094.table
  base := (408953389924165280862712101913009510217/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6084000000000000000000000000000000000000000
      center := (6201)
      previous := (0)
      next := (2925)
      square := (290586586672536173608927256568000000000000)
      linear := (-37575405873605438900997288663648000000000000)
      constant := (1217017853751246255440911834624302749860160228) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree094.table
  base := (4089533895824462607856648195022362200773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (62595)
      previous := (0)
      next := (28665)
      square := (2905865866725361736089272565680000000000000)
      linear := (-379255999652364440332952266395120000000000000)
      constant := (12397649516621516503709153111327856051629502932) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (142480992628938819457/50000000000000000000)
  centralHi := (56992397051575527783/20000000000000000000)
  directionLo := (57297988502509666299/20000000000000000000)
  directionHi := (35811242814068541437/12500000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree095.table
  base := (4452489525796673349063415876204890848857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (31005)
      previous := (0)
      next := (14625)
      square := (1452932933362680868044636282840000000000000)
      linear := (-189851527969776478761559923394920000000000000)
      constant := (6214524235790824436118867391280565277962222994) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree095.table
  base := (1113122380762589586073075035417665751643/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (62595)
      previous := (0)
      next := (28665)
      square := (2905865866725361736089272565680000000000000)
      linear := (-383242251546462051945279858248040000000000000)
      constant := (12661355536344335887580431583594399313731984048) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57297988502509666299/20000000000000000000)
  centralHi := (35811242814068541437/12500000000000000000)
  directionLo := (288009793721629582301/100000000000000000000)
  directionHi := (144004896860814791151/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree096.table
  base := (4820906266423266362693839725988611908009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (3445)
      previous := (0)
      next := (1625)
      square := (161436992595853429782737364760000000000000)
      linear := (-21314002952391751446459267052400000000000000)
      constant := (705035273557803035481959689645624150824907042) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree096.table
  base := (2410453132108179298816348474086708290311/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (6955)
      previous := (0)
      next := (3185)
      square := (322873985191706859565474729520000000000000)
      linear := (-43025389271173295950845272233440000000000000)
      constant := (1436425437937485524035896141031365229608500472) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (288009793721629582301/100000000000000000000)
  centralHi := (144004896860814791151/50000000000000000000)
  directionLo := (289521666543814985929/100000000000000000000)
  directionHi := (28952166654381498593/10000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree097.table
  base := (2597392038986263833082428258388680810719/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (31005)
      previous := (0)
      next := (14625)
      square := (1452932933362680868044636282840000000000000)
      linear := (-193800525173275047274706883548280000000000000)
      constant := (6477468947313180960335107163042386734052414396) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree097.table
  base := (2597392038099635498826406463239185786347/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (62595)
      previous := (0)
      next := (28665)
      square := (2905865866725361736089272565680000000000000)
      linear := (-391214755334657275169935041953880000000000000)
      constant := (13197069731638256487556605112105409412648270296) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell234.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (289521666543814985929/100000000000000000000)
  centralHi := (28952166654381498593/10000000000000000000)
  directionLo := (36378210665228654477/12500000000000000000)
  directionHi := (291025685321829235817/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree098.table
  base := (1114824583669959181987751222513090838137/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6084000000000000000000000000000000000000000
      center := (6201)
      previous := (0)
      next := (2925)
      square := (290586586672536173608927256568000000000000)
      linear := (-39155004755004866306256072724992000000000000)
      constant := (1322195738308326679857196709148428822329612754) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree098.table
  base := (5574122916925128366547409981596388763661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (62595)
      previous := (0)
      next := (28665)
      square := (2905865866725361736089272565680000000000000)
      linear := (-395201007228754886782262633806800000000000000)
      constant := (13469077906691018184971284043493852429238113524) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell234.Kernel098
