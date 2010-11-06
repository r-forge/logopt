\name{best.envelope}
\alias{best.envelope}
\title{ Best price at any moment in time }
\description{
  Calculate the time evolution of all assets based on the given prices
  relative and take the maximum at every time index.
}
\usage{
best.envelope(x)
}
\arguments{
  \item{x}{
        Time series of relative prices
}
}
\details{
  Perform a cumprod per column to recover the time series of each asset
  price, construct and return a time series with the best price at any
  time index.  Contrast to best.asset that shows
  the time evolution
  for the individual asset with the best terminal price.
}
\value{
  Time series of the best asset price any time index.
}
\author{ Marc Delvaux }
