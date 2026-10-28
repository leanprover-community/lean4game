import { useAtomValue } from 'jotai'
import { Trans, useTranslation } from 'react-i18next'
import { twMerge } from 'tailwind-merge'

import { mobileAtom } from '../state/preferences-atoms'
import { Announcements } from './Announcements'
import { GameTile } from './GameTile'
import { featuredGamesAtom } from './landing-atoms'
import { Section } from './Section'
import { ServerCapacity } from './ServerCapacity'

export function LandingPage() {
  const { t } = useTranslation()
  return (
    <div className="flex-col">
      <header
        className={twMerge(
          'flex-col gap-4 bg-linear-to-b from-primary to-cyan-400 px-4 py-12',
          'text-white',
        )}
        // style={{ backgroundImage: `url(${bgImage})` }}
      >
        <h1 className="m-0 text-white">{t('landing.title')}</h1>
        <p className="mx-auto w-full max-w-3xl text-center font-bold">
          <Trans
            i18nKey="landing.subtitle"
            components={{
              leanLink: (
                <a
                  className="text-white decoration-dotted"
                  href="https://leanprover-community.github.io/"
                  target="_blank"
                  rel="noreferrer"
                />
              ),
              mathlibLink: (
                <a
                  className="text-white decoration-dotted"
                  href="https://github.com/leanprover-community/mathlib4"
                  target="_blank"
                  rel="noreferrer"
                />
              ),
            }}
          />
        </p>
      </header>
      {/* the sections span the whole width, every second one has a background */}
      <div className="flex-col text-left [&>section:nth-of-type(odd)]:bg-(--section-bg)">
        <Announcements />
        <FeatureGamesList />
        <ServerCapacity />
        <Section title={t('landing.development.title')}>
          <p>
            <Trans
              i18nKey="landing.development.description"
              components={{
                issueLink: (
                  <a
                    href="https://github.com/leanprover-community/lean4game/issues"
                    target="_blank"
                    rel="noreferrer"
                  />
                ),
              }}
            />
          </p>
        </Section>
        <Section title={t('landing.newGames.title')}>
          <p>
            <Trans
              i18nKey="landing.newGames.template"
              components={{
                skeletonLink: (
                  <a
                    href="https://github.com/hhu-adam/GameSkeleton"
                    target="_blank"
                    rel="noreferrer"
                  />
                ),
                docsLink: (
                  <a
                    href="https://github.com/leanprover-community/lean4game/"
                    target="_blank"
                    rel="noreferrer"
                  />
                ),
              }}
            />
          </p>
          <p>{t('landing.newGames.featured')}</p>
        </Section>
        <Section title={t('landing.funding.title')}>
          <p>
            <Trans
              i18nKey="landing.funding.description"
              components={{
                adamLink: (
                  <a
                    href="https://hhu-adam.github.io"
                    target="_blank"
                    rel="noreferrer"
                  />
                ),
              }}
            />
          </p>
        </Section>
      </div>
    </div>
  )
}

/** The tiles of all games, in two columns on desktop */
function FeatureGamesList() {
  const { t } = useTranslation()
  const mobile = useAtomValue(mobileAtom)
  const { data: games, isPending, isError } = useAtomValue(featuredGamesAtom)

  if (isPending)
    return (
      <Section as="div">
        <p className="text-center">{t('landing.games.loading')}</p>
      </Section>
    )
  if (isError)
    return (
      <Section as="div">
        <p className="text-center">{t('landing.games.error')}</p>
      </Section>
    )

  const tiles = games.flatMap(game =>
    game.tile ? [{ ...game, tile: game.tile }] : [],
  )
  if (tiles.length === 0) {
    return (
      <Section as="div">
        <p className="text-center">
          {t('landing.games.none')}
          {import.meta.env.DEV && (
            <>
              <br />
              {t('landing.games.noneDev')}
            </>
          )}
        </p>
      </Section>
    )
  }
  return (
    <Section
      as="div"
      className={twMerge(
        'grid max-w-6xl gap-6',
        mobile ? 'grid-cols-1' : 'grid-cols-2',
      )}
    >
      {tiles.map(game => (
        <GameTile key={`${game.owner}/${game.repo}`} {...game} />
      ))}
    </Section>
  )
}
