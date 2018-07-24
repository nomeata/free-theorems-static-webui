


import FrontendTypeExpressionsTests as FrontendTypeExpressions (tests)
import FrontendCheckLocalTests as FrontendCheckLocal (tests)
import FrontendCheckGlobalTests as FrontendCheckGlobal (tests)
import FrontendOtherTests as FrontendOther (tests)
import ParserPrettyPrinterTests as ParserPrettyPrinter (tests)



-- | Run all tests defined for the FreeTheorems library.

main = do
  FrontendTypeExpressions.tests
  FrontendCheckLocal.tests
  FrontendCheckGlobal.tests
  FrontendOther.tests
  ParserPrettyPrinter.tests
  

