\name{worst.asset}
\alias{worst.asset}
\title{Time evolution of worst asset}
\description{
  Time evolution of the asset with the worst terminal price.
}
\usage{
worst.asset(x)
}
\arguments{
  \item{x}{
        Time series of relative prices.
}
}
\details{
  Perform a cumprod per column to recover the time series of each asset
  price, find the asset with worst terminal price and returns the
  corresponding price time series.  This corresponds to the price time
  series for the worst individual asset.
  Contrast with worst.envelope that construct a time series of the worst price at any time index, irrespective of the asset.
}
\value{
  Time series of the price for the asset with worst terminal price.
}

\author{ Marc Delvaux}