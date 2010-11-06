\name{worst.envelope}
\alias{worst.envelope}
\title{ Worst price at any moment in time }
\description{
  Calculate the time evolution of all assets based on the given prices
  relative and take the minimum at every time index.
}
\usage{
worst.envelope(x)
}
\arguments{
  \item{x}{
        Time series of relative prices
}
}
\details{
  Perform a cumprod per column to recover the time series of each asset
  price, construct and return a time series with the worst price at any
  time index.  Contrast to worst.asset that shows
  the time evolution
  for the individual asset with the worst terminal price.
}
\value{
  Time series of the worst asset price any time index.
}
\author{ Marc Delvaux }
