{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE StandaloneDeriving #-}

import Data.Traversable
import qualified Data.Text as T

import Reflex.Dom


import Language.Haskell.FreeTheorems
import Language.Haskell.FreeTheorems.Theorems (Theorem)

import FTTools
import KnownDeclarations

deriving instance Ord LanguageSubset
deriving instance Ord TheoremType

main :: IO ()
main = mainWidgetWithHead htmlHead $ do
    divClass "container" $ divClass "row" $ divClass "col" $ do
        el "h1" $ text "Free Theorems!"
        el "form" $ mdo
            dType <- divClass "form-group" $ do
                el "label" $
                    text "Please enter a (polymorphic) type, e.g. \"(a -> Bool) -> [a] -> [a]\":"
                fmap _textInput_value . textInput $ def
                   & textInputConfig_initialValue .~ "(a -> Bool) -> [a] -> [a]"
                   & textInputConfig_attributes .~ (return $ "class" =: "form-control")

            dmSig <- errorDiv $ (parseTypeString decls . T.unpack <$> dType)

            dModel <- divClass "form-group" $ do
                el "label" $ text "Please choose a sublanguage of Haskell:"
                fmap _dropdown_value $ dropdown BasicSubset (pure $ mconcat
                    [ BasicSubset =: "no bottoms (hence no general recursion and no selective strictness)"
                    , SubsetWithFix EquationalTheorem =: "general recursion but no selective strictness"
                    , SubsetWithFix InequationalTheorem =: "general recursion but no selective strictness, inequational theorems "
                    , SubsetWithSeq EquationalTheorem =: "general recursion and selective strictness"
                    , SubsetWithSeq InequationalTheorem =: "general recursion and selective strictness, inequational theorems"
                    ]) $ def
                   & dropdownConfig_attributes .~ (return $ "class" =: "form-control")

            -- dExtraDecls <- divClass "form-group" $ do
            --     el "label" $ text "If you need extra declarations, you can enter them here:"
            --     fmap _textArea_value . textArea $ def
            --        & textAreaConfig_initialValue .~ "myId :: a -> a"
            --        & textAreaConfig_attributes .~ (return $ "class" =: "form-control")

            let decls = knownDeclarations

            let dmIntermediate   = do
                    sig <- dmSig
                    model <- dModel
                    return $ interpret decls model =<< sig

            let dmTheorem        = fmap (prettyTheorem [] . asTheorem) <$> dmIntermediate
            let dmSpecialTheorem = fmap (prettyTheorem [] . asTheorem . specialiseAll) <$> dmIntermediate

            bootstrapCard "The Free Theroem" Nothing $
                el "pre" $
                    dynText $ (maybe "" (T.pack.show)) <$> dmTheorem

            bootstrapCard "The Free Theroem" (Just "with relations specialized to functions") $
                el "pre" $
                    dynText $ (maybe "" (T.pack.show)) <$> dmSpecialTheorem

            el "p" $ do
              text "This is an online interface to "
              elAttr "a" ("href" =: "http://hackage.haskell.org/package/free-theorems") $
                 text "the free-theorems Haskell package"
              text ". Source code for this UI at "
              elAttr "a" ("href" =: "https://github.com/nomeata/free-theorems-static-webui") $
                 text "https://github.com/nomeata/free-theorems-static-webui"
              text ". Contributions welcome!"

        return ()
  where
    htmlHead :: DomBuilder t m => m ()
    htmlHead = do
        el "style" (text css)
        elAttr "link" (mconcat
            [ "href" =: "https://maxcdn.bootstrapcdn.com/bootstrap/4.0.0/css/bootstrap.min.css"
            , "rel" =: "stylesheet"
            , "type" =: "text/css"
            , "integrity" =: "sha384-Gn5384xqQ1aoWXA+058RXPxPg6fy4IWvTNh0E263XmFcJlSAwiGgFAW/dAiS6JXm"
            , "crossorigin" =: "anonymous"
            ]) (return ())
        elAttr "meta" (mconcat
            [ "name" =: "viewport"
            , "content" =: "width=device-width, initial-scale=1, shrink-to-fit=no"
            ]) (return ())
        el "title" (text "Free Theorems!")


bootstrapCard :: DomBuilder t m => T.Text -> Maybe T.Text -> m a -> m a
bootstrapCard title subtitle inside = do
    divClass "card my-3" $ do
        elClass "h5" "card-title" $ text title
        for subtitle $ \t -> elClass "h6" "card-subtitle" $ text t
        divClass "card-body" $ inside

errorDiv :: (PostBuild t m, DomBuilder t m) =>
    Dynamic t (Either String a) ->
    m (Dynamic t (Maybe a))
errorDiv inp = do
    elDynAttr "div" (attribs <$> inp) (dynText $ either T.pack (const "") <$> inp)
    return $ (either (const Nothing) Just <$> inp)
  where
    attribs (Left _)  = "class" =: "alert alert-danger"
    attribs (Right _) = "display" =: "none"


css :: T.Text
css = T.unlines
    [ ""
    , ".theorem {"
    , "  font-family:mono;"
    , "  width:100%;"
    , "}"

    ]
