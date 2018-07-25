{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts #-}

import Data.Traversable
import Data.Maybe
import qualified Data.Text as T
import Control.Monad.IO.Class
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Class
import Control.Monad

import Reflex.Dom


import Language.Haskell.FreeTheorems
import Language.Haskell.FreeTheorems.Theorems (Theorem)

import FTTools
import KnownDeclarations

deriving instance Ord LanguageSubset
deriving instance Ord TheoremType

main :: IO ()
main = mainWidgetWithHead htmlHead $ do
    divClass "container" $ do
        elClass "h1" "display-1" $ text "Free Theorems!"
        el "form" $ mdo
            dType <- divClass "form-group" $ do
                el "label" $
                    text "Please enter a (polymorphic) type, e.g. \"(a -> Bool) -> [a] -> [a]\":"
                fmap _textInput_value . textInput $ def
                   & textInputConfig_initialValue .~ "(a -> Bool) -> [a] -> [a]"
                   & textInputConfig_attributes .~ (return $ "class" =: "form-control")

            dSig <- errorDiv $ do
                decls <- dDecls
                type_ <- T.unpack <$> dType
                return $ parseTypeString decls type_

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

            dExtraSrc <- divClass "form-group" $ do
                el "label" $ text "If you need extra declarations, you can enter them here:"
                fmap _textArea_value . textArea $ def
                   & textAreaConfig_initialValue .~ "data Unit = Unit"
                   & textAreaConfig_attributes .~ (return $ "class" =: "form-control")

            dExtraDecls <- errorDiv $ parseDeclarations knownDeclarations . T.unpack <$> dExtraSrc
            let dDecls = (knownDeclarations ++) . fromMaybe [] <$> runMaybeT dExtraDecls

            let dIntermediate   = joinMaybeT $
                    interpret <$> lift dDecls <*> lift dModel <*> dSig

            theoremCard Nothing
                dDecls dIntermediate
            theoremCard (Just "with relations specialized to functions")
                dDecls (specialiseAll <$> dIntermediate)
            let invCard = theoremCard (Just "with relations specialized to inverses of functions")
                    dDecls (specialiseAllInverse <$> dIntermediate)
            dyn_ $ when <$> (isInequational <$> dModel) <*> pure invCard

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

theoremCard variant dDecls dIntermediate = do
    bootstrapCard "The Free Theorem" variant $ do
        el "pre" $ do
            dynText $ fromMaybe "" <$> (runMaybeT $ T.pack.show <$> dTheorem)
        el "pre" $ do
            dynText $ fromMaybe "" <$> (runMaybeT $ T.pack <$> dLifts)
        el "pre" $ do
            dynText $ fromMaybe "" <$> (runMaybeT $ T.pack <$> dClasses)
  where
    dTheorem = prettyTheorem [] . asTheorem <$> dIntermediate
    dLifts   = (unlines . map show) <$> (unfoldLifts <$> lift dDecls <*> dIntermediate)
    dClasses = (unlines . map show) <$> (unfoldClasses <$> lift dDecls <*> dIntermediate)


-- | Errors are delayed, but successes go through immediatelly
-- Actually disabled for now, I like the snappy behaviour better
{-
delayError :: (PerformEvent t m, MonadHold t m, TriggerEvent t m, MonadIO (Performable m)) =>
    Dynamic t (Either a b) -> m (Dynamic t (Either a b))
delayError d = do
    delayedEvents <- delay 0.5 (updated d)
    d' <- holdDyn Nothing (Just <$> delayedEvents)
    return $ do
        now <- d
        past <- d'
        return $ case (past, now) of
            (Nothing, _)     -> now    -- before any delayed events arrive
            (_, Right _ )    -> now  -- current value is good
            (Just x, Left _) -> x -- current value is bad, delay
-}

bootstrapCard :: DomBuilder t m => T.Text -> Maybe T.Text -> m a -> m a
bootstrapCard title subtitle inside = do
    divClass "card my-3 p-2" $ do
        elClass "h5" "card-title" $ text title
        for subtitle $ \t -> elClass "h6" "card-subtitle" $ text t
        divClass "card-body" $ inside

errorDiv :: (PerformEvent t m, MonadHold t m, TriggerEvent t m, MonadIO (Performable m), PostBuild t m, DomBuilder t m) =>
    Dynamic t (Either String a) ->
    m (MaybeT (Dynamic t) a)
errorDiv inp = do
    elDynAttr "div" (attribs <$> inp) (dynText $ either T.pack (const "") <$> inp)
    return $ MaybeT $ either (const Nothing) Just <$> inp
  where
    attribs (Left _)  = "class" =: "alert alert-danger"
    attribs (Right _) = "display" =: "none"

joinMaybeT :: Functor m => MaybeT m (Maybe a) -> MaybeT m a
joinMaybeT = MaybeT . fmap join . runMaybeT

css :: T.Text
css = T.unlines
    [ ""
    , ".theorem {"
    , "  font-family:mono;"
    , "  width:100%;"
    , "}"

    ]
